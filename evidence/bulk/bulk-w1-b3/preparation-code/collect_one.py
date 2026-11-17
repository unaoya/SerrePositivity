"""Private collector: Lake options, sequential opens, recorded inspection budget."""
from pathlib import Path
import sys,tempfile,json,hashlib
r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(r/'scripts/refactor'));import bulk_collect as B;import klw1_namespace as K
root=Path(sys.argv[1]);source=sys.argv[2];dest=Path(sys.argv[3]);original=K.HERE
text=B.patched_helper((original/'klw1_collect_refs.lean').read_text());old='opts := Elab.async.set config.options.toOptions false';assert text.count(old)==1
text=text.replace(old,'opts := Elab.async.set (config.options.toOptions.set '+chr(96)+'maxHeartbeats (0 : Nat)) false')
with tempfile.TemporaryDirectory(prefix='b3-collector-') as directory:
 p=Path(directory);(p/'klw1_collect_refs.lean').write_text(text);K.HERE=p;K.collect(root,[source],dest)
for p in dest.glob('*.json'):
 if p.name=='files.json':continue
 d=json.load(open(p));d['elaboration']['inspection_resource_override']={'maxHeartbeats':0,'reason':'Synchronous inspection budget; mathematical source and Lake synthesis options are unchanged.'};d['elaboration']['helper_sha256']=hashlib.sha256(text.encode()).hexdigest();p.write_text(json.dumps(d,ensure_ascii=False))
