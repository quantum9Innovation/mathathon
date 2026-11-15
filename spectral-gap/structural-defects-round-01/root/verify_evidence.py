"""Check frozen evidence dependencies without running a worker scheduler."""
from pathlib import Path
from hashlib import sha256
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def validate(record, root=ROOT):
    nodes = record['nodes']
    topic = root.parent.resolve()
    visiting = set()
    finished = set()
    order = []
    checks = 0
    review_bindings = 0

    def artifact_path(name):
        path = (root/name).resolve()
        if not path.is_relative_to(topic):
            raise ValueError('Artifact lies outside the spectral topic: ' + name)
        if not path.is_file():
            raise ValueError('Artifact missing: ' + name)
        return path

    def visit(node_id):
        nonlocal checks, review_bindings
        if node_id in visiting:
            raise ValueError('Dependency cycle at ' + node_id)
        if node_id in finished:
            return
        if node_id not in nodes:
            raise ValueError('Missing dependency node: ' + node_id)
        node = nodes[node_id]
        visiting.add(node_id)
        for dependency in node['dependencies']:
            visit(dependency)
            if node['status']=='accepted' and nodes[dependency]['status']!='accepted':
                raise ValueError('Accepted node has an unaccepted dependency: ' + node_id)
        if node['status']=='accepted' and node['unresolved_findings']:
            raise ValueError('Accepted node has unresolved findings: ' + node_id)
        for artifact in node['artifacts']:
            path = artifact_path(artifact['path'])
            if digest(path)!=artifact['sha256']:
                raise ValueError('Artifact changed: ' + artifact['path'])
            checks += 1
        if node['kind']=='paper_proof' and node['status']=='accepted' and not node['reviews']:
            raise ValueError('Accepted paper proof has no recorded review: ' + node_id)
        for review in node['reviews']:
            path = artifact_path(review['path'])
            if digest(path)!=review['sha256']:
                raise ValueError('Review changed: ' + review['path'])
            text = path.read_text()
            for target in review['targets']:
                target_path = artifact_path(target['path'])
                if digest(target_path)!=target['sha256']:
                    raise ValueError('Reviewed target changed: ' + target['path'])
                if target['sha256'] not in text:
                    raise ValueError('Review does not bind its target hash: ' + review['path'])
                review_bindings += 1
            checks += 1
        visiting.remove(node_id)
        finished.add(node_id)
        order.append(node_id)

    for node_id in nodes:
        visit(node_id)
    return {'status':'passed','topological_order':order,'artifact_checks':checks,
            'review_target_bindings':review_bindings,
            'scope':'Consistency of recorded evidence only. Mathematical acceptance is a recorded judgment.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--record',type=Path,default=ROOT/'EVIDENCE_DAG.json')
    args = parser.parse_args()
    record = json.loads(args.record.read_text())
    result = validate(record)
    result['record_sha256'] = digest(args.record)
    result['validator_sha256'] = digest(Path(__file__))
    (ROOT/'EVIDENCE_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
