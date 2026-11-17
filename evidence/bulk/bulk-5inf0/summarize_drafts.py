#!/usr/bin/env python3
"""Summarize current draft checks; stale successes never count as PASS."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, state = args.root.resolve(), args.state.resolve()
    drafts = root / 'formalization-plans/bhatt-scholze/drafts'
    plan = json.loads(args.plan.read_text())
    memo = {}

    def status(name):
        if name in memo:
            return memo[name]
        path = state / ('validate-' + name.replace('/', '-') + '.json')
        if not path.exists():
            return 'NOT_RUN'
        record = json.loads(path.read_text())
        source = drafts / (name + '.lean')
        result = record['status']
        if not source.exists() or sha(source) != record['source_sha256']:
            result = 'NEEDS_RECHECK_SOURCE'
        elif result == 'PASS':
            artifact = Path(record['olean'])
            if not artifact.exists():
                result = 'NEEDS_RECHECK_ARTIFACT'
            elif record.get('olean_sha256') and sha(artifact) != record['olean_sha256']:
                result = 'NEEDS_RECHECK_ARTIFACT'
            else:
                for dep in record.get('dependency_signatures', []):
                    src = drafts / (dep['draft'] + '.lean')
                    out = state / 'validation/Bulk5InfDraft' / (dep['draft'] + '.olean')
                    if (not src.exists() or not out.exists()
                            or sha(src) != dep['source_sha256'] or sha(out) != dep['olean_sha256']):
                        result = 'NEEDS_RECHECK_DEPENDENCY'
                        break
                if result == 'PASS' and any(status(d) != 'PASS'
                                             for d in record['extra_public_imports']):
                    result = 'NEEDS_RECHECK_DEPENDENCY'
        memo[name] = result
        return result

    rows = [dict(draft=n, status=status(n), dependencies=plan['dependencies'][n],
                 protected_source=n == 'Shared/EInfinityPowerOperation') for n in plan['order']]
    result = dict(status='incomplete' if any(r['status'] != 'PASS' for r in rows) else 'PASS',
                  counts=dict(Counter(r['status'] for r in rows)), drafts=rows,
                  note='The plan includes unchanged auxiliary and protected inputs; scope is explicit per row.')
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result['counts'], ensure_ascii=False))


if __name__ == '__main__':
    main()
