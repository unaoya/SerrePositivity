from pathlib import Path
import json,sys
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(r/'scripts/refactor'));from layer_check import imports
mm=json.load(open(w/'module-map.json'));rev={v:k for k,v in mm.items()};report=json.load(open(w/'static-layers.json'));out=[]
for x in report['violations']:
 if x['kind']!='reverse-section':continue
 a,b=x['path'];old_a=rev.get(a,a);old_b=rev.get(b,b);p=w/'before'/Path(old_a.replace('.','/')+'.lean');present=p.exists() and old_b in imports(p.read_text());out.append({'from':a,'to':b,'before_from':old_a,'before_to':old_b,'exists_in_frozen_main':present,'source_moved_in_b3':old_a!=a,'target_moved_in_b3':old_b!=b})
(w/'baseline-section-edges.json').write_text(json.dumps(out,indent=2));print('preexisting',sum(x['exists_in_frozen_main'] for x in out),'/',len(out))
