from pathlib import Path
import json,gzip,hashlib,subprocess
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');b=w/'before';stage=w/'rendered';sha=lambda x:hashlib.sha256(x).hexdigest()
delta=json.load(open(w/'main-delta.json'));added={x['path'] for x in delta if x['status']=='A'};outputs=[];sources={};collisions=[]
for path in sorted(p for p in stage.rglob('*') if p.is_file()):
 rel=str(path.relative_to(stage));after=path.read_bytes();before=(b/rel).read_bytes() if (b/rel).exists() else None
 if rel in added:collisions.append(rel);continue
 if before==after:continue
 if before is not None:sources[rel]=sha(before)
 outputs.append({'source':rel if before is not None else None,'target':rel,'sha256':sha(after),'edits':[{'start':0,'stop':len(before or b''),'text':after.decode()}]})
assert not collisions,('New frozen-main files collide with B2 destinations',collisions)
deletions=json.load(open(w/'deletions.json'))
for rel in deletions:sources[rel]=sha((b/rel).read_bytes())
bundle={'schema_version':1,'math_base':json.load(open(w/'baseline.json'))['merged_before_migration'],'library_sha256':sha((b/'SerrePositivity/Util/Citation.lean').read_bytes()),'sources':sources,'outputs':outputs,'deletions':deletions}
with (w/'initial-rebased-bundle.json.gz').open('wb') as raw:
 with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as g:g.write(json.dumps(bundle,ensure_ascii=False,separators=(',',':')).encode())
(w/'application-plan.json').write_text(json.dumps({'outputs':len(outputs),'sources':len(sources),'deletions':len(deletions),'collisions':collisions,'frozen_main':json.load(open(w/'baseline.json'))['frozen_main'],'bundle_sha256':sha((w/'initial-rebased-bundle.json.gz').read_bytes()),'note':'Reconstructed against exact frozen sources; delta reference rewrites follow from original-environment compiler captures.'},indent=2));print('fresh-base bundle',len(outputs),len(deletions))
