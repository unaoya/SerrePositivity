"""Capture actual citation/tag metadata from compiled modules, without changing sources.
Run under one ordinary bounded bulk lease. This is not an axiom audit.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--modules',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=int,default=235);a=p.parse_args();root=a.root.resolve();a.output.mkdir(parents=True,exist_ok=True);modules=json.loads(a.modules.read_text());assert len(modules)==len(set(modules));assert all(m.startswith('SerrePositivity.') for m in modules);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for module in modules:assert (root/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')).exists(),module
registry=json.loads((root/'research/bibliography.json').read_text());keys=sorted(r['key'] for r in registry['references']);assert len(keys)==len(set(keys))
probe=a.output/'CitationProbe.lean';probe.write_text('import SerrePositivity.Util.Citation\n'+'\n'.join('import '+m for m in modules)+'\n'+'\n'.join('#cite_tags '+key for key in keys)+'\n');log=a.output/'native.log';started=time.monotonic();env=dict(os.environ,LEAN_NUM_THREADS='1')
with log.open('w') as out:result=subprocess.run(['gtimeout','--kill-after=3s',str(a.seconds),'lake','env','lean','--root='+str(a.output.resolve()),'--json',str(probe.resolve())],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
receipt=dict(returncode=result.returncode,seconds=time.monotonic()-started,modules=modules,keys=keys,source_sha256={m:sha(root/(m.replace('.','/')+'.lean')) for m in modules},citation_source_sha256=sha(root/'SerrePositivity/Util/Citation.lean'),bibliography_sha256=sha(root/'research/bibliography.json'),probe_sha256=sha(probe),log_sha256=sha(log),git_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),root=str(root),policy='Actual #cite_tags metadata for selected native defining modules; no axiom or preservation verdict')
(a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if result.returncode:raise SystemExit(result.returncode)
records=[];errors=[];all_records=0;selected=set(modules)
for line in log.read_text().splitlines():
 try:diagnostic=json.loads(line)
 except ValueError:continue
 if diagnostic.get('severity')=='error':errors.append(diagnostic)
 try:record=json.loads(diagnostic['data'])
 except (KeyError,ValueError,TypeError):continue
 if not isinstance(record,dict) or 'declaration' not in record:continue
 required={'key','number','edition','relation','comment','declaration','module','path','line'};assert required<=record.keys(),record;all_records+=1
 if record['module'] in selected:records.append(record)
assert not errors,errors[:2]
assert records,'No selected native citation records; refusing an empty metadata baseline'
summary=dict(records=records,count=len(records),all_imported_records=all_records,modules=modules,keys=keys,receipt_sha256=sha(a.output/'receipt.json'),policy='Multiplicity retained. Actual path/line kept as provenance; comparison transports actual defining module and canonical declaration name.')
(a.output/'complete.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');print(json.dumps(dict(selected_records=len(records),all_imported_records=all_records,seconds=receipt['seconds'],returncode=result.returncode)))
