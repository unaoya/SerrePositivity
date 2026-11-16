from pathlib import Path
import json,sys,collections,subprocess,hashlib
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import imports
base=json.loads((W/'tracked-import-graph.json').read_text());g={m:set(ds) for m,ds in base.items()}
# Overlay every tracked main increment and every actual B3prime addition/deletion, not only the prepared bundle.
changed=subprocess.check_output(['git','diff','32d364b53','HEAD','--name-only','--no-renames','--','SerrePositivity','SerrePositivity.lean'],cwd=R,text=True).splitlines()
for path in changed:
 if not path.endswith('.lean'):continue
 m=path[:-5].replace('/','.');p=R/path
 if p.exists():g[m]=imports(p.read_text())
 else:g.pop(m,None)
g={m:{d for d in ds if d.startswith('SerrePositivity')} for m,ds in g.items()}
missing=[{'module':m,'import':d} for m,ds in g.items() for d in ds if d not in g]
deg={m:len(ds) for m,ds in g.items()};rev=collections.defaultdict(set)
for m,ds in g.items():
 for d in ds:rev[d].add(m)
q=collections.deque(m for m,v in deg.items() if not v);removed=set()
while q:
 m=q.popleft();removed.add(m)
 for n in rev[m]:
  deg[n]-=1
  if not deg[n]:q.append(n)
def reach(seeds):
 seen=set(seeds);q=collections.deque(seeds)
 while q:
  for d in g.get(q.popleft(),set()):
   if d not in seen:seen.add(d);q.append(d)
 return seen
bs='SerrePositivity.BhattScholze';ei='SerrePositivity.EInfinity';mapping=json.loads((W/'B4/module-map.json').read_text());pub=json.loads((W/'full-preview-import-graph.json').read_text())['publication_targets'];root=reach(['SerrePositivity']);result={'baseline':'32d364b53','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'scope':'Original complete active import graph plus every git source delta through current HEAD, including incoming main; Archive exclusions unchanged.','modules':len(g),'source_delta_paths':len(changed),'missing_project_imports':missing,'cycle_residual':sorted(set(g)-removed),'EInfinity_to_BS':[{'module':m,'import':d} for m,ds in g.items() if m==ei or m.startswith(ei+'.') for d in ds if d==bs or d.startswith(bs+'.')],'EInfinity_transitively_reaches_BS':sorted(m for m in reach([ei]) if m==bs or m.startswith(bs+'.')),'publication_targets':[{'module':r['module'],'root_reachable':r['module'] in root} for r in pub]}
(W/'actual-import-graph.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));assert not missing and not result['cycle_residual'] and not result['EInfinity_to_BS'] and not result['EInfinity_transitively_reaches_BS'] and all(r['root_reachable'] for r in result['publication_targets']),result
old=json.loads(Path('/tmp/bulk-w1-b3/bs-section-order-check.json').read_text());rows=[]
for e in old['paper_section_reverse_edges']:
 a,b=mapping.get(e['from'],e['from']),mapping.get(e['to'],e['to']);assert a in g and b in g,(a,b)
 retained=b in g[a]
 if retained:decision='retained mathematical dependency; original approved reason and compiler references remain applicable after owner/name transport'
 elif e['to'].endswith('.Almost.SupportedQuotient'):decision='resolved paper-section reversal: SupportedQuotient relocated adjacent to ExcisionTor in section8'
 elif e['from'].endswith('.Derived.Excision'):decision='resolved paper-section reversal: actual integral existence prerequisite factored into Interface; section10 existence body placed in Almost'
 else:decision='original direct edge removed or factored; inspect actual imports and declaration owners'
 # Same direct import can cease to reverse paper order because target subject was corrected.
 if retained and e['to'].endswith('.Almost.SupportedQuotient'):
  retained=False;decision='resolved paper-section reversal by approved move of SupportedQuotient next to ExcisionTor; direct mathematical dependency preserved'
 if retained and e['to'].endswith('.Derived.IntegralExistence'):
  retained=True;decision='retained mixed-subject interface dependency: the split removes general initial-limit and bridge components, but the residual integral existence still derives the Theorem10.11/Corollary8.14 consequence from the E3 interface; do not claim this section-order edge resolved'
 rows.append({**e,'current_from':a,'current_to':b,'direct_import_still_present':b in g[a],'original_reverse_edge_retained':retained,'B3prime_disposition':decision,'current_project_imports':sorted(g[a])})
ledger={'original_edges':34,'retained_original_reverse_edges':sum(r['original_reverse_edge_retained'] for r in rows),'resolved_original_reverse_edges':sum(not r['original_reverse_edge_retained'] for r in rows),'policy':'This reconciles all34 approved B3 paper-order edges, not a tier exemption. No original tier exceptions are changed. Original compiler refs and reasons retained; graph is actual source.','rows':rows};(W/'actual-bs-reverse-edge-ledger.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2));print({k:v for k,v in result.items() if not isinstance(v,list)});print('BS original34:',ledger['resolved_original_reverse_edges'],'resolved,',ledger['retained_original_reverse_edges'],'retained')
for r in rows:
 if not r['original_reverse_edge_retained']:print(r['current_from'],'=>',r['current_to'],r['B3prime_disposition'])
