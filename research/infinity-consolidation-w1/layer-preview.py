"""Read-only KL-W1 layer preview on the stage0 graph; never writes layers.json."""
from pathlib import Path
import sys,json,csv,pickle,copy,collections
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'scripts/refactor'))
from klw1_layer_check import check
from layer_check import under
_,raw=pickle.loads(Path('/private/tmp/ic-w1-stage0-graph.pickle').read_bytes())
c=json.loads((ROOT/'scripts/refactor/layers.json').read_text())['klw1'];g={m:ds for m,ds in raw.items() if not any(under(m,p) for p in c['exclude_prefixes'])}
unknown=[m for m in g if under(m,'SerrePositivity.InfinityCategories') and m not in c['modules']]
result={'missing_baseline_tiers':unknown,'method':'existing checker with temporary Consumers fallback only for absent baseline metadata; no config edits'}
for m in unknown:c['modules'][m]='Consumers'
try:
 before=check(g,c)
 moves={r['old_module']:r['new_module'] for r in csv.DictReader((OUT/'moves.csv').open())}
 def move(m):return moves.get(m,m)
 afterg={move(m):{move(d) for d in ds} for m,ds in g.items()}
 afterc=copy.deepcopy(c);afterc['modules']={move(m):v for m,v in c['modules'].items()}
 for m in moves:afterc['modules'][move(m)]=c['modules'].get(m,'Consumers')
 # Preserve the implementation status of every old module at exact-module granularity.
 afterc['implementation_prefixes']+= [move(m) for m in moves if any(under(m,p) for p in c['implementation_prefixes'])]
 for k in ('implementation_edges','reverse_edges'):
  for r in afterc[k]:r['from']=move(r['from']);r['to']=move(r['to'])
 after=check(afterg,afterc)
 old={json.dumps(v,sort_keys=True) for v in before['violations']}
 expected={json.dumps({'kind':v['kind'],'path':tuple(move(m) for m in v['path'])},sort_keys=True) for v in before['violations']}
 actual={json.dumps(v,sort_keys=True) for v in after['violations']}
 result.update(baseline_count=len(old),preview_count=len(actual),new=[json.loads(v) for v in sorted(actual-expected)],removed=[json.loads(v) for v in sorted(expected-actual)],baseline_kinds=dict(collections.Counter(v['kind'] for v in before['violations'])),preview_kinds=dict(collections.Counter(v['kind'] for v in after['violations'])))
except ValueError as e:result['metadata_error']=str(e)
(OUT/'layer-preview.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps(result,ensure_ascii=False,indent=2))
