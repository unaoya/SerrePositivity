"""署名台帳の構造・依存DAG・既存宣言の所在を検査する（Leanの型検査ではない）。"""
from pathlib import Path
import collections
import hashlib
import json
import re
import sys

root = Path(__file__).resolve().parents[2]
ledger = Path(__file__).with_name('inf-supply-signatures-1117.json')
x = json.loads(ledger.read_text())
rows = x['signatures']
rendered = ledger.with_suffix('.md').read_text()
# Gate display must match the machine ledger, including estimates used at the 29,000-line boundary.
status_lines = ["<!-- current-signature-state:begin -->", "## 最新の進行状態と停止判定", "",
    f"既計上の累計：{x['verified_lean_lines']:,}行。外枠：{x['final_cap']:,}行。係数：{x['factor']}。",
    "行別の実測は既計上の補助・共有検証組を含みうるため、合計して累計を作り直さない。",
    "この表が進行状態・残り見込みの現在値。後の各節は署名の型・設計・検証履歴を保持する。", "",
    "|署名ID|状態|実測または部分計上|残り（素）|残り（係数2）|",
    "|---|---|---:|---:|---:|"]
for row in rows:
    bare = row['bare_lines'] if row['status'] != 'verified' else [0, 0]
    corrected = row['corrected_lines'] if row['status'] != 'verified' else [0, 0]
    actual = row.get('actual_lines', '—') if row['status'] == 'verified' else row.get('partial_verified_lean_lines', '—')
    status_lines.append(f"|{row['id']}|{row['status']}|{actual}|{bare[0]}〜{bare[1]}|{corrected[0]}〜{corrected[1]}|")
status_lines += ["", "<!-- current-signature-state:end -->"]
status_table = "\n".join(status_lines)
if '--sync' in sys.argv:
    sys.argv.remove('--sync')
    marker = r'<!-- current-signature-state:begin -->.*?<!-- current-signature-state:end -->'
    if re.search(marker, rendered, re.S):
        rendered = re.sub(marker, lambda _: status_table, rendered, count=1, flags=re.S)
    else:
        first_break = rendered.index('\n') + 1
        rendered = rendered[:first_break] + '\n' + status_table + '\n' + rendered[first_break:]
    ledger.with_suffix('.md').write_text(rendered)
assert status_table in rendered, 'stale Markdown status or estimate table: rerun checker with --sync'

ids = [r['id'] for r in rows]
assert len(ids) == len(set(ids)), 'duplicate signature ID'
assert len({r['name'] for r in rows}) == len(rows), 'duplicate declaration name'
by_id = {r['id']: r for r in rows}
indegree = {n: 0 for n in ids}
children = collections.defaultdict(list)
references = {}
for r in rows:
    assert r['status'] in {'pending', 'verified', 'deferred_next_checkpoint'}
    assert r['full_type'].startswith('∀ '), r['id']
    assert '```lean\n' + r['full_type'] + '\n```' in rendered, r['id']
    assert not re.search(r'\bsorry\b|\.\.\.|…|\?_', r['full_type']), r['id']
    assert r['corrected_lines'] == [2 * n for n in r['bare_lines']], r['id']
    assert 0 <= r['bare_lines'][0] <= r['bare_lines'][1]
    assert r['existing'] and r['literature'], r['id']
    assert len(r['dependencies']) == len(set(r['dependencies'])), r['id']
    for d in r['dependencies']:
        assert d in by_id, (r['id'], 'unknown dependency', d)
        children[d].append(r['id'])
        indegree[r['id']] += 1
    for ref in r['existing']:
        p = root / ref['path']
        lines = p.read_text().splitlines()
        line = lines[ref['line'] - 1]
        assert re.search(r'\b' + re.escape(ref['name']) + r'\b', line), ref
        references[ref['path']] = hashlib.sha256(p.read_bytes()).hexdigest()
queue = collections.deque(n for n in ids if indegree[n] == 0)
order = []
while queue:
    n = queue.popleft()
    order.append(n)
    for c in children[n]:
        indegree[c] -= 1
        if indegree[c] == 0:
            queue.append(c)
assert len(order) == len(ids), ('dependency cycle', [n for n in ids if indegree[n]])
active = [r for r in rows if r['status'] == 'pending']
deferred = [r for r in rows if r['status'] == 'deferred_next_checkpoint']
def total(rs, key):
    return [sum(r[key][i] for r in rs) for i in range(2)]
result = {
    'success': True,
    'validation': 'JSON structure / current rendered status and estimates / rendered complete signatures / reference name at source line / Kahn topological sort',
    'lean_type_elaboration': 'not run; paper signatures, unimplemented signatures not certified',
    'signature_count': len(rows),
    'verified_count': sum(r['status'] == 'verified' for r in rows),
    'additional_count': sum(r['additional_mathematics'] for r in rows),
    'deferred_count': len(deferred),
    'edge_count': sum(len(r['dependencies']) for r in rows),
    'acyclic': True,
    'topological_order': order,
    'active_bare_lines': total(active, 'bare_lines'),
    'active_corrected_lines': total(active, 'corrected_lines'),
    'deferred_corrected_lines': total(deferred, 'corrected_lines'),
    'active_completion_corrected_lines': [x['verified_lean_lines'] + a for a in total(active, 'corrected_lines')],
    'ledger_sha256': hashlib.sha256(ledger.read_bytes()).hexdigest(),
    'reference_source_sha256': references,
}
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'reference_source_sha256'}, ensure_ascii=False, indent=2))
