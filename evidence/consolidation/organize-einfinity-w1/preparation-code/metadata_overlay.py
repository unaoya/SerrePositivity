"""Overlay reviewed citation tags and unchanged formal-audit coverage on a preview.
This does not apply anything to the working tree or alter a mathematical proof.
"""
from pathlib import Path
import argparse,csv,json,re,sys,hashlib
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--preview',type=Path,required=True);p.add_argument('--before',type=Path,required=True);a=p.parse_args();root=a.root.resolve();base=root/'evidence/consolidation/organize-einfinity-w1';mm=json.loads((base/'module-map.json').read_text());plan=json.loads((base/'namespace-rewrite-map.json').read_text());public={r['old']:r['new'] for r in plan['rows'] if not r['old'].startswith('_private.')};sources={r['old_module']:r for r in csv.DictReader((base/'stage1-modules.csv').open())};records=[]
original={str(p.relative_to(a.preview)):hashlib.sha256(p.read_bytes()).hexdigest() for p in a.preview.rglob('*.lean')}
sys.path.insert(0,str(root/'scripts/refactor'));from layer_check import code_only
# All 99 original module docstrings receive exactly the same stopped-route status.
status='状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。'
for r in sources.values():
 if r['id']!='OE05':continue
 f=a.preview/r['new_path']
 if not f.exists():continue
 text=f.read_text()
 if status not in text:
  assert '/-!' in text;text=text.replace('/-!','/-!\n'+status,1);f.write_text(text)
 records.append(dict(path=r['new_path'],change='D81 stopped route status in module docstring'))
# Existing own Kerodon and partial HA citations are retained by compiler rewriting.
citations=json.loads((base/'preparation/citation-review-all-native.json').read_text())['records']
for row in citations:
 if row['existing_source_attribute']:continue
 assert row['key']=='kerodon' and row['status']=='partial';f=a.preview/row['new_path']
 if not f.exists():continue
 text=f.read_text();name=public[row['declaration']];comment=row['planned_comment'];attribute='attribute [kerodon '+row['tag']+' '+json.dumps(comment,ensure_ascii=False)+'] _root_.'+name
 if attribute not in text:
  if 'import Mathlib.Tactic.CrossRefAttribute' not in text:
   assert text.startswith('module\n');text=text.replace('module\n','module\npublic import Mathlib.Tactic.CrossRefAttribute\n',1)
  text=text.rstrip()+'\n\n'+attribute+'\n';f.write_text(text)
 records.append(dict(path=row['new_path'],change='native Kerodon tag with explicit partial comment',tag=row['tag'],declaration=name))
# Quoted Name literals in audit registries are metadata, not resolved term refs.
for path in ['scripts/audit_einfinity.lean','scripts/audit_bhatt_scholze_stage2.lean']:
 f=a.preview/path
 if not f.exists():continue
 text=f.read_text();mask=code_only(text);edits=[]
 for match in re.finditer(r"(?<![`\w])(`{1,2})(SerrePositivity(?:\.[\w']+)+)",mask):
  old=match[2]
  if old in public:edits.append((match.start(2),match.end(2),public[old]))
 for lo,hi,new in reversed(edits):text=text[:lo]+new+text[hi:]
 records.append(dict(path=path,change='native-owned quoted Name literals',occurrences=len(edits)))
 if path=='scripts/audit_einfinity.lean':
  old='    unless (`SerrePositivity.EInfinity).isPrefixOf mod do continue'
  roots=['SerrePositivity.EInfinity','SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight','SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom','SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization']
  singles=[r['new_module'] for r in sources.values() if r['id']=='OE03' and r['new_module'].startswith('SerrePositivity.InfinityCategories.Kerodon.')];assert len(singles)==2
  replacement='    unless (#[\n'+',\n'.join('        `'+s for s in roots)+'] : Array Name).any (fun scopePrefix ↦ scopePrefix.isPrefixOf mod) ||\n      (#[\n'+',\n'.join('        `'+s for s in sorted(singles))+'] : Array Name).contains mod do continue'
  if old in text:
   assert text.count(old)==1;text=text.replace(old,replacement)
  else:assert replacement in text
  def included(m):return any(m==p or m.startswith(p+'.') for p in roots) or m in singles
  def before(m):return m=='SerrePositivity.EInfinity' or m.startswith('SerrePositivity.EInfinity.')
  allmods=[str(p.relative_to(a.before).with_suffix('')).replace('/','.') for p in (a.before/'SerrePositivity').rglob('*.lean')]
  unexpected=[m for m in allmods if before(m)!=included(mm.get(m,m))];assert not unexpected,unexpected
  records.append(dict(path=path,change='preserve original axiom-audit scope under module map',original_modules=sum(map(before,allmods)),transported_modules=sum(included(mm.get(m,m)) for m in allmods),unexpected=[]))
 f.write_text(text)
changes={str(p.relative_to(a.preview)):dict(before_sha256=original[str(p.relative_to(a.preview))],after_sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in a.preview.rglob('*.lean') if hashlib.sha256(p.read_bytes()).hexdigest()!=original[str(p.relative_to(a.preview))]}
(a.preview/'metadata-overlay.manifest.json').write_text(json.dumps(changes,indent=2)+'\n')
(a.preview/'metadata-overlay.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n');print('metadata overlay records',len(records))
