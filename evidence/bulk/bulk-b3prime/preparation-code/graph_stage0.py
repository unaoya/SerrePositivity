from pathlib import Path
import json,re,sys,collections,time
R=Path.cwd();D=R/'evidence/bulk/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
t=time.monotonic();pat=re.compile(r'(?m)^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(SerrePositivity(?:\.[\w]+)*)')
g={};rev=collections.defaultdict(set)
for p in [R/'SerrePositivity.lean',*(R/'SerrePositivity').rglob('*.lean')]:
 n=str(p.relative_to(R))[:-5].replace('/','.');g[n]=set(pat.findall(code_only(p.read_text())))
 for c in g[n]:rev[c].add(n)
mods=json.loads((D/'module-map.proposed.json').read_text())['rows'];names=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];splits=json.loads((D/'split-plan.proposed.json').read_text())['rows'];seeds={m['old_module'] for m in mods}|{n['old_module'] for n in names}|{s['old_path'][:-5].replace('/','.') for s in splits}
q=collections.deque(seeds);affected=set(seeds)
while q:
 for c in rev[q.popleft()]:
  if c not in affected:affected.add(c);q.append(c)
q=collections.deque(['SerrePositivity']);reachable={'SerrePositivity'}
while q:
 for c in g.get(q.popleft(),set()):
  if c not in reachable:reachable.add(c);q.append(c)
leafs=['SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.'+n for n in ['PerfectPrism','RawCompletion','Source']]+['SerrePositivity.BhattScholze.Semiperfectoid.PerfectPrismDivisionComparison','SerrePositivity.BhattScholze.Andre.Envelope.PDivisionSource','SerrePositivity.BhattScholze.Perfectoidization.TensorCompatibility']
x={'status':'static direct imports and reverse closure; no build or preservation claims','baseline':'32d364b53','modules':len(g),'changed_owner_seed_count':len(seeds),'reverse_closure_count':len(affected),'reverse_closure':sorted(affected),'root_reachable_count':len(reachable),'publication_targets':[{'module':n,'already_root_reachable':n in reachable,'proposed':'add new mapped path to aggregate; retain mathematically meaningful proved alternative/endpoint, no unused-declaration deletion'} for n in leafs],'seconds':time.monotonic()-t};(D/'stage0-import-closure.json').write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n');print('modules',len(g),'seeds',len(seeds),'reverse closure',len(affected),'root',len(reachable));print([(x['module'],x['already_root_reachable']) for x in x['publication_targets']])
