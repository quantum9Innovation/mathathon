"""Durable checkpoint transport for bounded workers."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import time
import uuid

try:
    from .research_runner import atomic_json, validate_reply
except ImportError:
    from research_runner import atomic_json, validate_reply


REPLY_SCHEMA = json.loads((Path(__file__).parent / "pilot/reply.schema.json").read_text())
MAX_CHECKPOINT_BYTES = 256 * 1024
MAX_CHECKPOINTS = 256
MAX_EVIDENCE_BYTES = 256 * 1024


def checkpoint_mcp_overrides(checkpoint_dir, deadline=None, evidence_manifest=None):
    """Return invocation settings to insert before the worker's trailing input marker."""
    arguments = [str(Path(__file__).resolve()), "--directory", str(Path(checkpoint_dir).resolve())]
    if deadline is not None:
        arguments += ["--deadline", str(float(deadline))]
    tools = ["save_checkpoint", "remaining_budget"]
    if evidence_manifest is not None:
        arguments += ["--evidence-manifest", str(Path(evidence_manifest).resolve())]
        tools += ["list_evidence", "read_evidence"]
    settings = "{command=" + json.dumps(sys.executable) + ",args=" + json.dumps(arguments)
    settings += ',env_vars=[],enabled_tools=' + json.dumps(tools) + ',startup_timeout_sec=5,tool_timeout_sec=10'
    settings += ',tools={' + ",".join(name + '={approval_mode="approve"}' for name in tools) + '}}'
    return ["-c", "mcp_servers.checkpoint=" + settings]


def validate_schema(value, schema):
    expected = schema["type"]
    if expected == "object":
        if not isinstance(value, dict):
            raise ValueError("Checkpoint field must be an object")
        if set(value) != set(schema["required"]):
            raise ValueError("Checkpoint object has missing or unknown fields")
        for key, child in schema["properties"].items():
            validate_schema(value[key], child)
    elif expected == "array":
        if not isinstance(value, list):
            raise ValueError("Checkpoint field must be a list")
        for child in value:
            validate_schema(child, schema["items"])
    elif expected == "string" and not isinstance(value, str):
        raise ValueError("Checkpoint field must be text")
    elif expected == "boolean" and not isinstance(value, bool):
        raise ValueError("Checkpoint field must be boolean")
    if "enum" in schema and value not in schema["enum"]:
        raise ValueError("Checkpoint field has an invalid classification")


class CheckpointStore:
    def __init__(self, directory):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True)

    def save(self, checkpoint):
        validate_schema(checkpoint, REPLY_SCHEMA)
        validate_reply(checkpoint)
        if len((json.dumps(checkpoint, indent=2) + "\n").encode()) > MAX_CHECKPOINT_BYTES:
            raise ValueError("Checkpoint exceeds the receipt size limit")
        with (self.directory / ".checkpoint.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            numbers = [int(match.group(1)) for path in self.directory.iterdir()
                       if (match := re.fullmatch(r"checkpoint-(\d+)\.json", path.name))]
            if len(numbers) >= MAX_CHECKPOINTS:
                raise ValueError("Checkpoint directory reached the receipt count limit")
            number = max(numbers, default=0) + 1
            receipt = f"checkpoint-{number:06d}.json"
            temporary = self.directory / f".checkpoint-{uuid.uuid4().hex}"
            try:
                atomic_json(temporary, checkpoint)
                os.link(temporary, self.directory / receipt)
                descriptor = os.open(self.directory, os.O_RDONLY)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
            finally:
                temporary.unlink(missing_ok=True)
            return {"receipt": receipt}


class EvidenceCatalog:
    def __init__(self, manifest):
        mapping = json.loads(Path(manifest).read_text())
        if not isinstance(mapping, dict):
            raise ValueError("Evidence manifest must map ids to absolute file paths")
        self.paths = {}
        self.metadata = {}
        self.hashes = {}
        for key, value in mapping.items():
            expected_hash = None
            if isinstance(value, dict):
                if (set(value) != {"path", "sha256"} or not isinstance(value["sha256"], str) or
                        not re.fullmatch(r"[0-9a-f]{64}", value["sha256"])):
                    raise ValueError("Structured evidence requires an absolute path and SHA256 hash")
                expected_hash = value["sha256"]
                value = value["path"]
            if not isinstance(key, str) or not key or not isinstance(value, str) or not Path(value).is_absolute():
                raise ValueError("Evidence manifest requires nonempty ids and absolute file paths")
            path = Path(value)
            if path.is_symlink() or (expected_hash is not None and any(parent.is_symlink() for parent in path.parents)):
                raise ValueError("Evidence entries cannot be symbolic links")
            path = path.resolve(strict=True)
            with self.open_file(path) as stream:
                metadata = os.fstat(stream.fileno())
                if expected_hash is not None:
                    if metadata.st_size > MAX_EVIDENCE_BYTES:
                        raise ValueError("Frozen evidence exceeds the complete read limit")
                    if hashlib.sha256(stream.read(MAX_EVIDENCE_BYTES + 1)).hexdigest() != expected_hash:
                        raise ValueError("Frozen evidence hash changed")
            self.paths[key] = path
            self.metadata[key] = metadata
            self.hashes[key] = expected_hash

    @staticmethod
    def open_file(path):
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            os.close(descriptor)
            raise ValueError("Evidence entry must be a regular file")
        return os.fdopen(descriptor, "rb")

    def list(self, offset=0, limit=100):
        if type(offset) is not int or offset < 0 or type(limit) is not int or not 1 <= limit <= 200:
            raise ValueError("Evidence listing requires a nonnegative integer offset and integer limit from 1 to 200")
        keys = sorted(self.paths)
        selected = keys[offset:offset + limit]
        next_offset = offset + len(selected)
        return {"evidence": [{"id": key, "bytes": self.metadata[key].st_size} for key in selected],
                "next_offset": next_offset if next_offset < len(keys) else None}

    def read(self, identifier):
        if not isinstance(identifier, str) or identifier not in self.paths:
            raise ValueError("Unknown evidence id")
        path = self.paths[identifier]
        expected_hash = self.hashes[identifier]
        if expected_hash is not None and any(parent.is_symlink() for parent in path.parents):
            raise ValueError("Frozen evidence paths cannot contain symbolic links")
        with self.open_file(path) as stream:
            current = os.fstat(stream.fileno())
            original = self.metadata[identifier]
            fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns")
            if any(getattr(current, field) != getattr(original, field) for field in fields):
                raise ValueError("Evidence file changed after manifest loading")
            data = stream.read(MAX_EVIDENCE_BYTES)
            if expected_hash is not None and hashlib.sha256(data).hexdigest() != expected_hash:
                raise ValueError("Frozen evidence hash changed")
        return {"id": identifier, "text": data.decode("utf-8", errors="replace"),
                "bytes": len(data), "truncated": original.st_size > len(data)}


def tool_result(value, error=False):
    return {"content": [{"type": "text", "text": json.dumps(value)}], "isError": error}


def tool_definitions(evidence=False):
    tools = [{"name": "save_checkpoint", "description": "Durably save current partial work before continuing reasoning. Receipt confirms local persistence.",
             "inputSchema": {"type": "object", "properties": {"checkpoint": REPLY_SCHEMA},
                             "required": ["checkpoint"], "additionalProperties": False}},
            {"name": "remaining_budget", "description": "Return seconds remaining before the current call deadline.",
             "inputSchema": {"type": "object", "properties": {}, "additionalProperties": False}}]
    if evidence:
        tools += [{"name": "list_evidence", "description": "List ids and sizes of prior evidence supplied for this task.",
                   "inputSchema": {"type": "object", "properties": {
                       "offset": {"type": "integer", "minimum": 0},
                       "limit": {"type": "integer", "minimum": 1, "maximum": 200}}, "additionalProperties": False}},
                  {"name": "read_evidence", "description": "Read one prior evidence item by its exact listed id.",
                   "inputSchema": {"type": "object", "properties": {"id": {"type": "string"}},
                                   "required": ["id"], "additionalProperties": False}}]
    return tools


def serve(directory, input_stream=None, output_stream=None, deadline=None, evidence_manifest=None):
    input_stream = sys.stdin if input_stream is None else input_stream
    output_stream = sys.stdout if output_stream is None else output_stream
    store = CheckpointStore(directory)
    evidence = EvidenceCatalog(evidence_manifest) if evidence_manifest is not None else None

    def send(response):
        output_stream.write(json.dumps(response) + "\n")
        output_stream.flush()

    for line in input_stream:
        try:
            request = json.loads(line)
        except (ValueError, RecursionError):
            send({"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "Invalid JSON"}})
            continue
        if not isinstance(request, dict) or request.get("jsonrpc") != "2.0" or not isinstance(request.get("method"), str):
            send({"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "Invalid request"}})
            continue
        if "id" not in request:
            continue
        try:
            params = request.get("params", {})
            if not isinstance(params, dict):
                raise ValueError("Request parameters must be an object")
            method = request["method"]
            if method == "initialize":
                result = {"protocolVersion": params.get("protocolVersion", "2024-11-05"),
                          "capabilities": {"tools": {}},
                          "serverInfo": {"name": "research-checkpoints", "version": "1.0"}}
            elif method == "tools/list":
                result = {"tools": tool_definitions(evidence is not None)}
            elif method == "ping":
                result = {}
            elif method == "tools/call" and params["name"] == "remaining_budget":
                if params.get("arguments", {}):
                    raise ValueError("remaining_budget accepts no arguments")
                result = tool_result({"remaining_seconds": None if deadline is None else max(0, deadline - time.time())})
            elif method == "tools/call" and evidence is not None and params["name"] == "list_evidence":
                arguments = params.get("arguments", {})
                if not isinstance(arguments, dict) or not set(arguments) <= {"offset", "limit"}:
                    raise ValueError("list_evidence accepts only offset and limit arguments")
                result = tool_result(evidence.list(**arguments))
            elif method == "tools/call" and evidence is not None and params["name"] == "read_evidence":
                arguments = params.get("arguments", {})
                if not isinstance(arguments, dict) or set(arguments) != {"id"}:
                    raise ValueError("read_evidence requires only the id argument")
                result = tool_result(evidence.read(arguments["id"]))
            elif method != "tools/call" or params["name"] != "save_checkpoint":
                raise ValueError("Unknown tool")
            else:
                arguments = params.get("arguments", {})
                if set(arguments) != {"checkpoint"}:
                    raise ValueError("save_checkpoint requires only the checkpoint argument")
                result = tool_result(store.save(arguments["checkpoint"]))
        except (ValueError, TypeError, KeyError, OSError, RecursionError) as error:
            result = tool_result({"error": str(error)}, error=True)
        send({"jsonrpc": "2.0", "id": request["id"], "result": result})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--deadline", type=float)
    parser.add_argument("--evidence-manifest", type=Path)
    arguments = parser.parse_args()
    serve(arguments.directory, deadline=arguments.deadline, evidence_manifest=arguments.evidence_manifest)


if __name__ == "__main__":
    main()
