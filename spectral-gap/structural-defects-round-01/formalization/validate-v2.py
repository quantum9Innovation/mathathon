from argparse import ArgumentParser
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess
import tempfile
import time


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = ArgumentParser()
    parser.add_argument('--revision', choices=['v2'], default='v2')
    parser.add_argument('--packages-root', type=Path,
                        default=Path('/home/acru/angelo/proj/sadim/lean/.lake/packages'))
    parser.add_argument('--lean', type=Path,
                        default=Path('/home/acru/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    source = root / ('source-' + args.revision)
    output = root / ('validation-' + args.revision)
    output.mkdir(exist_ok=True)
    (output / 'CHECK.json').unlink(missing_ok=True)
    bindings = json.loads((root / ('SOURCE_MANIFEST-' + args.revision + '.json')).read_text())
    for name, expected in bindings['source_hashes'].items():
        assert digest(source / name) == expected, f'Source changed: {name}'

    version = subprocess.run([str(args.lean), '--version'], capture_output=True,
                             text=True, check=True, timeout=15).stdout.strip()
    assert 'Lean (version 4.31.0,' in version, version
    dependencies = json.loads((source / 'lake-manifest.json').read_text())
    revisions = {}
    library_paths = []
    for package in dependencies['packages']:
        path = args.packages_root / package['name']
        observed = subprocess.run(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                  capture_output=True, text=True, check=True,
                                  timeout=15).stdout.strip()
        assert observed == package['rev'], f'Dependency revision differs: {package["name"]}'
        revisions[package['name']] = observed
        compiled = path / '.lake/build/lib/lean'
        if package['name'] == 'mathlib':
            assert compiled.is_dir(), f'Missing compiled dependency: {compiled}'
        if compiled.is_dir():
            library_paths.append(str(compiled))

    env = dict(os.environ)
    env['LEAN_PATH'] = ':'.join(library_paths)
    env.pop('LEAN_SYSROOT', None)
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    receipt = {
        'manifest_sha256': digest(root / ('SOURCE_MANIFEST-' + args.revision + '.json')),
        'validator_sha256': digest(Path(__file__).resolve()),
        'compiler_sha256': digest(args.lean),
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'toolchain_version': version,
        'source_hashes': bindings['source_hashes'],
        'dependency_revisions': revisions,
        'dependency_cache_rebuilt': False,
        'bounded_per_source': {'threads': 2, 'memory_mb': 4096, 'timeout_seconds': 120},
        'files': {},
        'scope': 'Finite motif energy, inverse-constructed lift, exact cancellation eigenspace star attachment and finite arrow Schur correction only. No random-graph theorem.'
    }
    with tempfile.TemporaryDirectory(prefix='spectral-lean-', dir=output) as temporary:
        env['LEAN_PATH'] = temporary + ':' + ':'.join(library_paths)
        for name in bindings['compile_order']:
            path = source / name
            content = path.read_text()
            assert re.search(r'\b(sorry|admit|axiom|unsafe)\b', content) is None, name
            assert all(char not in content for char in ['\u2013', '\u2014', chr(59)]), name
            expected_theorems = re.findall(r'^theorem\s+(\w+)', content, re.MULTILINE)
            command = [str(args.lean), '-j2', '-M4096', '-o',
                       str(Path(temporary) / (path.stem + '.olean')), str(path)]
            start = time.monotonic()
            result = subprocess.run(command, cwd=source, env=env, capture_output=True,
                                    text=True, timeout=120)
            log = result.stdout + result.stderr
            (output / (path.stem + '.log')).write_text(log)
            assert result.returncode == 0, log
            assert 'warning:' not in log, log
            axioms = {}
            for declaration, items in re.findall(r"'(?:GrowingDefects|StructuralDefects)\.(\w+)' depends on axioms: \[([^]]*)\]", log):
                names = {item.strip() for item in items.split(',') if item.strip()}
                assert names <= allowed_axioms, (declaration, names)
                axioms[declaration] = sorted(names)
            assert set(axioms) == set(expected_theorems), (name, expected_theorems, axioms)
            receipt['files'][name] = {
                'reused_source': name in bindings.get('reused_sources', {}),
                'return_code': result.returncode,
                'elapsed_seconds': round(time.monotonic() - start, 3),
                'theorem_axioms': axioms,
                'compiled_output_generated': True,
                'compiled_output_retained': False,
                'log_sha256': digest(output / (path.stem + '.log'))
            }
            print(f'{name}: {len(axioms)} theorem checks passed')
    receipt['new_checked_declarations'] = sum(len(record['theorem_axioms'])
        for record in receipt['files'].values() if not record['reused_source'])
    receipt['reused_checked_declarations'] = sum(len(record['theorem_axioms'])
        for record in receipt['files'].values() if record['reused_source'])
    receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
    receipt['status'] = 'passed'
    (output / 'CHECK.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('All source bindings, dependency revisions and axiom checks passed')


if __name__ == '__main__':
    main()
