"""Validate stage0 inventories without invoking Lean or changing sources."""
from pathlib import Path
import csv,json,hashlib,re,collections,subprocess
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
rows=list(csv.DictReader((OUT/'moves.csv').open()))
assert len(rows)==2264
assert len({r['old_path'] for r in rows})==2264
assert len({r['new_path'] for r in rows})==2264
for r in rows:
 assert (ROOT/r['old_path']).is_file(),r['old_path']
 assert not (ROOT/r['new_path']).exists(),r['new_path']
 assert hashlib.sha256((ROOT/r['old_path']).read_bytes()).hexdigest()==r['sha256'],r['old_path']
assert collections.Counter(r['classification'] for r in rows)=={'一般':890,'BE固有':1047,'E∞の一般論':327}
assert sum(int(r['lines']) for r in rows)==165536
names=list(csv.DictReader((OUT/'source-name-hints.csv').open()))
assert len(names)==7414 and all(r['old_name']!=r['new_name'] for r in names)
assert len({r['old_name'] for r in names})==7412
assert len({r['new_name'] for r in names})==7412
assert next(r for r in names if r['old_name']=='SerrePositivity.EInfinity.Operad')['new_name'].endswith('.DGOperads.Operad')
assert len(list(csv.DictReader((OUT/'dg-classification.csv').open())))==473
assert len(list(csv.DictReader((OUT/'infinity-files.csv').open())))==15972
assert len(list(csv.DictReader((OUT/'root-outside-audit.csv').open())))==4332
prior=json.loads((OUT/'choose-inherited.json').read_text())['definitions'];assert len(prior)==255
assert all(r['replacement_lines_estimate']==[0,0] for r in prior)
a=json.loads((OUT/'choose-additional-review.json').read_text())
assert len(a['definitions'])==366 and a['summary']=={'不明':356,'対象外':4,'要らない':6}
assert all('original_source' not in r for r in json.loads((OUT/'choose-new-candidates.json').read_text())['definitions'])
lay=json.loads((OUT/'layer-preview.json').read_text());assert not lay['new'] and not lay['removed']
assert lay['baseline_count']==lay['preview_count']==172
for p in OUT.glob('*.py'):compile(p.read_text(),str(p),'exec')
report=ROOT/'formalization-plans/stage-ii/consolidation/report-infinity-consolidation.md'
for f in [report,OUT/'README.md']:
 for dest in re.findall(r'\]\(([^)]+)\)',f.read_text()):
  if not dest.startswith(('https:','http:','#')):assert (f.parent/dest).exists(),dest
changed=subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=ROOT,text=True).splitlines()
assert not any(p.endswith('.lean') for p in changed),changed
print('PASS: paper inventories, 2264 source SHAs, module/name proposal counts, links, Python syntax; no Lean execution')
