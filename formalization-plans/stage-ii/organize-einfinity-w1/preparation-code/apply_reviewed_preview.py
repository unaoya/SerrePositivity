"""Apply only a complete, unblocked, byte-verified OE-W1 preview. Dry run by default."""
from pathlib import Path
import argparse,csv,hashlib,json,os,subprocess
from reviewed_ilean import previews as reviewed_ilean_previews
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--preview',type=Path,required=True);p.add_argument('--progress',type=Path,required=True);p.add_argument('--layers',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--apply',action='store_true');a=p.parse_args();root=a.root.resolve();before=a.before.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
assert subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip()=='refactor/organize-einfinity'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=before,text=True).strip()=='30ae8948f339beec42d9340feb02f2031c22c72b'
core=set(read(Path('/private/tmp/oe-w1-reference-candidates/core-files.json')));stable=read(base/'preparation/unchanged-scope-files.json');required_core=len(core)-len(stable)
citation_check=read(base/'preparation/citation-review-baseline-check.json');assert citation_check['passed']
citation_receipt=read(base/'preparation/citation-before-receipt.json');assert sha((root/'SerrePositivity/Util/Citation.lean').read_bytes())==citation_receipt['citation_source_sha256'];assert sha((root/'research/bibliography.json').read_bytes())==citation_receipt['bibliography_sha256']
progress=read(a.progress);assert progress['complete'] and progress['completed_files']==progress['total_files']==required_core
assert read(a.preview/'review.json')=={}
summary=read(a.preview/'summary.json');assert summary['plan_sha256']==sha((base/'namespace-rewrite-map.json').read_bytes())
manifest=read(a.preview/'manifest.json');by={r['old_path']:r for r in manifest};assert len(by)==len(manifest)==required_core+2,'Complete core previews and 2 actual night audit captures required'
individual=reviewed_ilean_previews(before);assert {r['old_path'] for r in manifest if r.get('evidence')}==set(individual)
assert summary['individually_reviewed_ilean_files']==len(individual)==progress['individually_reviewed_ilean_files']
assert progress['compiler_captured_files']+len(individual)==required_core
expected=set(read(Path('/private/tmp/oe-w1-reference-candidates/core-files.json')))-set(read(base/'preparation/unchanged-scope-files.json'));expected.update(['scripts/audit_einfinity.lean','scripts/audit_bhatt_scholze_stage2.lean']);assert set(by)==expected
new_paths={r['new_path'] for r in manifest};assert len(new_paths)==len(manifest)
assert {str(p.relative_to(a.preview)) for p in a.preview.rglob('*.lean')}==new_paths
stable=read(base/'preparation/unchanged-scope-files.json');scope=list(csv.DictReader((base/'stage1-modules.csv').open()));moves=[r for r in scope if r['action']=='move'];assert len(moves)==456
assert {r['old_path'] for r in scope}<=set(by)|set(stable)
assert set(read(a.preview/'metadata-overlay.manifest.json'))<=new_paths
overlay=read(a.preview/'metadata-overlay.manifest.json');writes={};deletes=[];unchanged=[]
for r in manifest:
 old,new=r['old_path'],r['new_path'];assert not old.startswith(('drafts/','SerrePositivity/BhattScholze/'))
 original=(before/old).read_bytes();assert sha(original)==r['source_sha256'];assert (root/old).read_bytes()==original,old
 data=(a.preview/new).read_bytes();planned=r['preview_sha256']
 if new in overlay:
  assert overlay[new]['before_sha256']==planned;planned=overlay[new]['after_sha256']
 assert sha(data)==planned,new
 if old in individual:assert data==individual[old][0] and r['evidence']=='individually-reviewed-original-ilean-spans'
 if old!=new:assert not (root/new).exists();deletes.append(old)
 if old!=new or data!=original:writes[new]=data
 else:unchanged.append(old)
for path,digest in stable.items():assert sha((root/path).read_bytes())==sha((before/path).read_bytes())==digest
layers=root/'scripts/refactor/layers.json';assert layers.read_bytes()==(before/'scripts/refactor/layers.json').read_bytes();config=read(layers);config['klw1']=read(a.layers);writes['scripts/refactor/layers.json']=(json.dumps(config,ensure_ascii=False,indent=2)+'\n').encode()
assert set(deletes)=={r['old_path'] for r in moves}
impact=read(base/'branch-impact.json');assert impact['total_affected_with_worktree']<=30
record=dict(applied=False,reviewed_previews=len(manifest),base='30ae8948f339beec42d9340feb02f2031c22c72b',branch_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),compiler_previews=sum(r.get('evidence')!='individually-reviewed-original-ilean-spans' for r in manifest),individually_reviewed_ilean_previews=sum(r.get('evidence')=='individually-reviewed-original-ilean-spans' for r in manifest),unchanged_stable=len(stable),unchanged_captured=len(unchanged),source_moves=len(deletes),paths_to_write={path:sha(data) for path,data in writes.items()},paths_to_delete=sorted(deletes),plan_sha256=summary['plan_sha256'],layer_proposal_sha256=sha(a.layers.read_bytes()),preview_manifest_sha256=sha((a.preview/'manifest.json').read_bytes()),overlay_manifest_sha256=sha((a.preview/'metadata-overlay.manifest.json').read_bytes()))
a.output.mkdir(parents=True,exist_ok=True)
if a.apply:
 # Validate all inputs before the first write; publish destinations before removing originals.
 for path,data in writes.items():
  target=root/path;target.parent.mkdir(parents=True,exist_ok=True);temp=target.with_name(target.name+'.oe-w1-new');assert not temp.exists();temp.write_bytes(data);os.replace(temp,target)
 for path in deletes:(root/path).unlink()
 record['applied']=True
 for path,digest in stable.items():assert sha((root/path).read_bytes())==digest
 for path,digest in record['paths_to_write'].items():assert sha((root/path).read_bytes())==digest
record_path=a.output/('application.json' if a.apply else 'application-dry-run.json');record_path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n');(a.output/'paths-to-stage.nul').write_bytes(b''.join(p.encode()+b'\0' for p in sorted(set(writes)|set(deletes))));print(json.dumps({k:record[k] for k in ['applied','reviewed_previews','compiler_previews','individually_reviewed_ilean_previews','unchanged_stable','unchanged_captured','source_moves']}|{'written':len(writes)}))
