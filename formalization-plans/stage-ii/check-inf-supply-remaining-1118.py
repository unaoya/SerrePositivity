"""11-18の紙の範囲・完全な型の掲載・集計・DAGを検査する。Leanは起動しない。"""
from pathlib import Path
import collections
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
ledger = Path(__file__).with_name('inf-supply-signatures-1117.json')
doc = ledger.with_suffix('.md').read_text()
x = json.loads(ledger.read_text())
meta = x['remaining_plan_1118']
base = json.loads(subprocess.check_output([
    'git', 'show', meta['start_commit'] + ':' + str(ledger.relative_to(root))], cwd=root))
parents = {r['id']: r for r in base['signatures'] if r['status'] != 'verified'}
assert set(parents) == {'R04', 'R05', 'R06', 'R08', 'R09-Cech', 'R09', 'R12a',
    'R12b', 'R13b', 'R14', 'R15-Unit', 'R15a', 'R15b', 'R15c', 'R16', 'R17'}
rows = x['signatures']
by_id = {r['id']: r for r in rows}
assert len(by_id) == len(rows) == 93
paper = [r for r in rows if r.get('paper_only')]
assert len(paper) == 54
assert {r['proof_unit_parent'] for r in paper} == set(parents)
for ident, old in parents.items():
    new = by_id[ident]
    assert (old['name'], old['full_type']) == (new['name'], new['full_type']), ident
    assert new['pre_decomposition_1118'] == {k: old[k]
        for k in ['dependencies', 'bare_lines', 'corrected_lines']}, ident
    assert hashlib.sha256(new['full_type'].encode()).hexdigest() == meta['terminal_type_sha256'][ident]
for old in base['signatures']:
    if old['status'] == 'verified':
        assert by_id[old['id']] == old, ('verified row changed', old['id'])
assert x['verified_lean_lines'] == base['verified_lean_lines'] == 28221
assert x['factor'] == base['factor'] == 2
assert x['final_cap'] == base['final_cap'] == 29000
assert sum(r['additional_mathematics'] for r in rows) == 58
assert len([r for r in rows if r['status'] == 'verified']) == 39
active = [r for r in paper if r['status'] == 'pending']
deferred = [r for r in paper if r['status'] == 'deferred_next_checkpoint']
assert (len(active), len(deferred)) == (42, 12)

def sums(rs, key):
    return [sum(r[key][i] for r in rs) for i in [0, 1]]

for group, rs in [('active', active), ('coverage', deferred), ('combined', paper)]:
    assert sums(rs, 'bare_lines') == meta[group + '_bare']
    assert sums(rs, 'corrected_lines') == meta[group + '_corrected']
    upper = meta[group + '_corrected'][1]
    budget = meta['budget_proposals'][group + '_additional']
    assert 1.01 * upper <= budget <= 1.05 * upper
for row in paper:
    assert row['full_type'].startswith('∀ ')
    assert not re.search(r'\bsorry\b|\.\.\.|…|\?_', row['full_type'])
    assert '\n```lean\n' + row['full_type'] + '\n```' in doc
    assert row['corrected_lines'] == [2 * n for n in row['bare_lines']]
    assert row['existing'] and row['literature'] and row['method'] and row['specified_compatibility']
    for ref in row['existing']:
        lines = (root / ref['path']).read_text().splitlines()
        assert re.search(r'\b' + re.escape(ref['name']) + r'\b', lines[ref['line'] - 1]), ref
for row in meta['choices']:
    assert hashlib.sha256((root / row['path']).read_bytes()).hexdigest() == row['source_sha256']
    assert row['selection_source'] and row['specified_compatibility'] and row['decision']
    assert row['replacement_lines'] == [0, 0]
# Complete graph, including verified anchors and all new prerequisite laws.
indegree = {r['id']: len(r['dependencies']) for r in rows}
children = collections.defaultdict(list)
for row in rows:
    assert len(row['dependencies']) == len(set(row['dependencies']))
    for dep in row['dependencies']:
        assert dep in by_id, (row['id'], dep)
        children[dep].append(row['id'])
q = collections.deque(k for k, v in indegree.items() if v == 0)
order = []
while q:
    ident = q.popleft()
    order.append(ident)
    for child in children[ident]:
        indegree[child] -= 1
        if indegree[child] == 0:
            q.append(child)
assert len(order) == len(rows), ('cycle', [k for k, v in indegree.items() if v])
lean_diff = subprocess.check_output(['git', 'diff', '--name-only', meta['start_commit'],
    '--', '*.lean'], cwd=root, text=True).splitlines()
assert not lean_diff, ('Lean changed during paper goal', lean_diff)
old_drafts = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard',
    '--', '*.lean'], cwd=root, text=True).splitlines()
prefix = 'SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/Cocompletion/'
assert set(old_drafts) == {prefix + 'HomWeightYonedaUnit' + n + '.lean'
    for n in ['PointEvaluation', 'Square', 'SquareNormalized', 'Values']}
result = {'success': True, 'paper_only': True, 'lean_elaboration': 'not run',
    'build_and_lock': 'not invoked', 'verified': 39, 'total': len(rows), 'additional': 58,
    'parents': 16, 'paper_units': len(paper), 'active_units': len(active), 'deferred_units': len(deferred),
    'original_16_terminal_types_unchanged': True, 'verified_39_rows_unchanged': True,
    'factor_and_29000_checkpoint_unchanged': True, 'acyclic': True,
    'graph_edges': sum(len(r['dependencies']) for r in rows), 'topological_order': order,
    'active_bare': sums(active, 'bare_lines'), 'active_corrected': sums(active, 'corrected_lines'),
    'coverage_bare': sums(deferred, 'bare_lines'), 'coverage_corrected': sums(deferred, 'corrected_lines'),
    'combined_corrected': sums(paper, 'corrected_lines'), 'budget_proposals': meta['budget_proposals'],
    'choice_points_reviewed': len(meta['choices']), 'lean_diff_since_start': lean_diff,
    'old_draft_sha256': {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in old_drafts},
    'ledger_sha256': hashlib.sha256(ledger.read_bytes()).hexdigest()}
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['topological_order', 'old_draft_sha256']},
    ensure_ascii=False, indent=2))
