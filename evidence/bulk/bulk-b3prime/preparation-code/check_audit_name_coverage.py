from pathlib import Path
import json,re,sys,collections,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
names=json.loads((W/'public-comparison-name-map.json').read_text());names['SerrePositivity.Inputs.exists_perfectoidization_of_finite']='SerrePositivity.BhattScholze.exists_perfectoidization_of_finite';lookup=collections.defaultdict(set)
for a,b in names.items():
 if a==b:continue
 parts=a.split('.')
 for i in range(len(parts)):lookup['.'.join(parts[i:])].add((a,b))
rx=re.compile(r"(?<![\w.])(?:_root_\.)?[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*");result=[];sources={}
for path in json.loads((W/'all-audit-inventory.json').read_text())['audits']:
 raw=(R/path).read_bytes();sources[path]=hashlib.sha256(raw).hexdigest();s=code_only(raw.decode());hits=[]
 for m in rx.finditer(s):
  token=m[0].removeprefix('_root_.')
  if token in lookup:hits.append({'token':token,'line':s.count('\n',0,m.start())+1,'targets':sorted(lookup[token])})
 if hits:result.append({'path':path,'hits':hits})
report={'scope':'All106 formal audits, comment/string-free full identifier and every qualified suffix scan against all nonidentity original public names, including wrapper redirect; exact ownership checked separately in native B4 table. Not a substitute for formal execution.','audits':len(sources),'source_sha256':sources,'remaining_candidates':result};(W/'audit-name-coverage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2));print('audit name scan106 remaining',len(result));print([(r['path'],[(h['token'],h['line']) for h in r['hits']]) for r in result]);raise SystemExit(bool(result))
