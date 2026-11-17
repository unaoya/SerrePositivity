"""Select original source capture candidates from native .ilean references plus literal fallbacks."""
from pathlib import Path
from collections import Counter
import argparse,csv,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--plan-root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
plan=json.loads((a.plan_root/'namespace-rewrite-map.json').read_text());owners=json.loads((a.plan_root/'public-owner-map.json').read_text())['rows'];moving={m for m,n in plan['modules'].items() if m!=n};changed={(r['old_module'],r['old_kernel_name']) for r in owners if r['old_module']!=r['new_module'] or r['old']!=r['new']}
selected={m.replace('.','/')+'.lean':{'scope'} for m in plan['modules']};lib=root/'.lake/build/lib/lean';ilean_hits={};authored=set()
for m in moving:
 path=lib/(m.replace('.','/')+'.ilean')
 if path.exists():authored.update(json.loads(path.read_text())['decls'])
be_leaves={r['old'].rsplit('.',1)[-1] for r in owners if not r['private'] and '.BarrattEccles.' in r['old_module'] and r['old_kernel_name'] in authored and r['old']!=r['new']}
needles=set(moving)|{'SerrePositivity.EInfinity.'+s for s in ['HomotopyWeight','FrameHom','SimplicialLocalization']}
needles.update(be_leaves)
def trie_pattern(terms):
 tree={}
 for term in terms:
  node=tree
  for ch in term:node=node.setdefault(ch,{})
  node[None]={}
 def render(node):
  if None in node:return ''
  parts=[re.escape(ch)+render(child) for ch,child in sorted(node.items())]
  return parts[0] if len(parts)==1 else '(?:'+'|'.join(parts)+')'
 return render(tree)
literal=re.compile(trie_pattern(needles)+r'|\b(?:FrameHom|FrameArrows|HomotopyWeight|SimplicialLocalization|AnodyneWeakDetection)\b')
paths=subprocess.check_output(['git','ls-files','--','*.lean'],cwd=root,text=True).splitlines();eligible=[s for s in paths if (s=='SerrePositivity.lean' or s.startswith('SerrePositivity/') or s.startswith('scripts/')) and '/Archive/' not in s]
missing=[]
for rel in eligible:
 path=root/rel;data=path.read_text()
 if literal.search(data):selected.setdefault(rel,set()).add('literal')
 ip=lib/Path(rel).with_suffix('.ilean')
 if not ip.exists():missing.append(rel);continue
 x=json.loads(ip.read_text());hits=[]
 if any(v[0] in moving for v in x['directImports']):selected.setdefault(rel,set()).add('native-import')
 for key in x['references']:
  c=json.loads(key).get('c')
  if c and (c['m'],c['n']) in changed:hits.append((c['m'],c['n']))
 if hits:selected.setdefault(rel,set()).add('native-reference');ilean_hits[rel]=hits
files=sorted(selected);(out/'files.json').write_text(json.dumps(files,indent=2)+'\n');(out/'reasons.json').write_text(json.dumps({f:sorted(selected[f]) for f in files},indent=2)+'\n');(out/'native-reference-hits.json').write_text(json.dumps(ilean_hits,indent=2)+'\n');summary=dict(eligible_source_files=len(eligible),selected_files=len(files),owned_scope_files=len(plan['modules']),selected_native_reference_files=len(ilean_hits),missing_baseline_ilean_files=len(missing),selection_reasons=dict(Counter(v for reasons in selected.values() for v in reasons)),drafts='excluded from application; B4 impact recorded separately',policy='ILEAN native owner/name references plus exact names and partial namespaces; original compiler capture validates spans/bindings before rewriting');(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(out/'missing-ilean.json').write_text(json.dumps(missing,indent=2)+'\n');print(json.dumps(summary))
