"""Separate paper section ordering from five dependency tiers."""
from pathlib import Path
import json,sys,re,collections
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');V=R;sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import imports
prefix='SerrePositivity.BhattScholze.'
def section(m):
 if m=='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence':return 10,'§10' # module docstring: author Theorem 10.11; retained path is explicitly authorized
 p=m.removeprefix(prefix)
 for start,rank,label in [('Delta.',2,'§2'),('Prism.',3,'§3'),('Prismatic.Site.',3.5,'§3.12/4.1'),('Prismatic.Envelopes.',4,'§4'),('Prismatic.CechAlexander.',4,'§4'),('Prismatic.HodgeTate.Affine.',4,'§4.2'),('Prismatic.Crystalline.',5,'§5'),('Prismatic.HodgeTate.Comparison.',6,'§6'),('Andre.',7,'§7'),('Semiperfectoid.',7,'§7'),('Perfectoidization.',8,'§8'),('IntegralPerfectoidization.',10,'§10'),('Almost.',10,'§10'),('PerfectoidIdeal.',10,'§10')]:
  if p.startswith(start):return rank,label
 return None
edges=[];unclassified=[];bs={str(p.relative_to(V))[:-5].replace('/','.') for p in (V/'SerrePositivity/BhattScholze').rglob('*.lean')}
for m in sorted(bs):
 if section(m) is None:unclassified.append(m)
 for d in sorted(imports((V/(m.replace('.','/')+'.lean')).read_text())):
  if not d.startswith(prefix) or section(m) is None or section(d) is None:continue
  if section(d)[0]>section(m)[0]:edges.append({'from':m,'to':d,'from_section':section(m)[1],'to_section':section(d)[1],'status':'paper-section reversal; inspect actual declarations separately from tier violation'})
low=[e for e in edges if e['from'].startswith(prefix+'Delta.')];result={'modules':len(bs),'paper_section_reverse_edges':edges,'unclassified_aggregate_or_inputs':unclassified,'delta_to_later_sections':low,'note':'Section order is an inventory, not a five-tier error rule; retain explicit mathematical dependencies with reasons.'};(W/'bs-section-order-check.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('BS files',len(bs),'section reversals',len(edges),'Delta reversals',len(low))
for e in low:print(e['from'], '->', e['to'])
