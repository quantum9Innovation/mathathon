"""Exercise rejection controls for the frozen evidence consistency checker."""
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import json

from verify_evidence import validate

ROOT = Path(__file__).resolve().parents[1]


def main():
    record = json.loads((ROOT / 'EVIDENCE_DAG.json').read_text())
    controls = []

    def rejected(name, mutate):
        altered = deepcopy(record)
        mutate(altered)
        try:
            validate(altered)
        except ValueError as error:
            controls.append({'name': name, 'status': 'rejected', 'reason': str(error)})
        else:
            raise AssertionError('Invalid record was accepted: ' + name)

    rejected('changed_artifact', lambda d: d['nodes']['vector_port']['artifacts'][0].update(sha256='0' * 64))
    rejected('missing_dependency', lambda d: d['nodes']['vector_port']['dependencies'].append('absent_node'))
    rejected('changed_review_target', lambda d: d['nodes']['vector_port']['reviews'][0]['targets'][0].update(sha256='0' * 64))
    rejected('unaccepted_premise', lambda d: d['nodes']['prior_results'].update(status='pending'))
    rejected('unresolved_finding', lambda d: d['nodes']['vector_port']['unresolved_findings'].append('unresolved_control'))
    rejected('dependency_cycle', lambda d: d['nodes']['problem']['dependencies'].append('vector_port'))
    rejected('missing_review', lambda d: d['nodes']['vector_port'].update(reviews=[]))
    result = {'status': 'passed', 'scope': 'Deliberately invalid in-memory records only. Source files are unchanged.',
              'record_sha256': sha256((ROOT / 'EVIDENCE_DAG.json').read_bytes()).hexdigest(),
              'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(), 'controls': controls}
    (ROOT / 'EVIDENCE_CONTROLS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
