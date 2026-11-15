from pathlib import Path
import json,subprocess,os,time,hashlib,sys
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');side=sys.argv[1];budget=int(sys.argv[2]);start=time.monotonic();root=R;plan=json.loads((W/'citation-baseline-plan.json').read_text());mapping=json.loads((W/'preservation-module-plan.json').read_text()) if side=='after' else {'modules':{},'declarations':{}};owners=set()
for m in plan['attribute_application_modules']:
 if m=='SerrePositivity.Inputs.Perfectoidization':
  if side=='before':owners.add(m)
  continue
 owners.add(mapping['modules'].get(m,m));owners.update(mapping.get('declarations',{}).get(m,{}).values())
owners=sorted(owners);groups=[owners[i:i+64] for i in range(0,len(owners),64)];out=W/'citation-metadata'/'actual';out.mkdir(parents=True,exist_ok=True);env=dict(os.environ,LEAN_NUM_THREADS='1');paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);env['LEAN_PATH']=os.pathsep.join(str((Path(p) if Path(p).is_absolute() else root/p).resolve()) for p in paths)
if side=='before':assert str(R/'.lake/build/lib/lean') in env['LEAN_PATH'] and str(A/'.lake/build/lib/lean') not in env['LEAN_PATH']
lean=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip())/'bin/lean'
def run(label,cmd):
 left=int(budget-(time.monotonic()-start)-10)
 if left<40:raise SystemExit(75)
 with (out/(label+'.log')).open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(min(left,180)),*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode in [124,137] and left<180:raise SystemExit(75)
 if r.returncode:raise SystemExit(r.returncode)
 return out/(label+'.log')
for i,modules in enumerate(groups):
 receipt=out/f'{i:03}.json';signature=hashlib.sha256(json.dumps({'source_modules':{m:hashlib.sha256((root/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in modules},'side':side,'after_manifest_sha256':hashlib.sha256((W/'final-bundle/manifest.json').read_bytes()).hexdigest() if side=='after' else None,'plan_sha256':hashlib.sha256((W/'citation-baseline-plan.json').read_bytes()).hexdigest()},sort_keys=True).encode()).hexdigest()
 if receipt.exists():
  previous=json.loads(receipt.read_text())
  if previous['signature']==signature:continue
  receipt.rename(receipt.with_name(receipt.stem+'.stale-'+previous['signature'][:12]+'.json'))
 run(f'{i:03}-build',['lake','build',*modules]);probe=out/f'Probe{i:03}.lean';probe.write_text('import SerrePositivity.Util.Citation\n'+'\n'.join('import '+m for m in modules)+'\n'+'\n'.join('#cite_tags '+key for key in plan['keys'])+'\n');t=time.monotonic();log=run(f'{i:03}-query',[str(lean),'--json',str(probe)]);records=[]
 for line in log.read_text().splitlines():
  try:diagnostic=json.loads(line);record=json.loads(diagnostic['data'])
  except (ValueError,KeyError,TypeError):continue
  if isinstance(record,dict) and 'declaration' in record:
   required={'key','number','declaration','module','relation','comment','edition','path','line'};assert required<=record.keys(),record
   if record['module'].startswith('SerrePositivity.'):records.append(record)
 receipt.write_text(json.dumps({'modules':modules,'signature':signature,'seconds':time.monotonic()-t,'records':records},ensure_ascii=False));print(side,i,len(records),flush=True)
 if budget-(time.monotonic()-start)<40:raise SystemExit(75)
summary={'side':side,'groups':len(groups),'application_owners':len(owners),'records_by_identity':{}};unique={};conflicts=[]
for i in range(len(groups)):
 for r in json.loads((out/f'{i:03}.json').read_text())['records']:
  key=json.dumps([r['key'],r['number'],r['declaration'],r['relation'],r['comment'],r['edition']],ensure_ascii=False);value={k:r[k] for k in ['key','number','declaration','module','relation','comment','edition','path','line']}
  if key in unique and unique[key]!=value:conflicts.append({'key':key,'before':unique[key],'after':value})
  unique[key]=value
assert unique,'native citation decoder produced no project-owned records'
summary.update(records=list(unique.values()),conflicts=conflicts);(out/'complete.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print(side,'complete',len(unique),'conflicts',len(conflicts),flush=True);raise SystemExit(bool(conflicts))
