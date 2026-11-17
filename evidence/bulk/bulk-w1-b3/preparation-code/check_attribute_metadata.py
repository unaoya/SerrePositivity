from pathlib import Path
import json,subprocess,os,time,collections,hashlib
W=Path('/tmp/bulk-w1-b3');V=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');start=time.monotonic();out=W/'attribute-metadata';out.mkdir(exist_ok=True);rows=[r for r in json.loads((W/'attribute-declaration-final.json').read_text()) if r['action']=='attach'];owners=sorted({r['new_module'] for r in rows});keys=sorted({r['key'] for r in rows});groups=[owners[i:i+64] for i in range(0,len(owners),64)];editions={r['key']:r['edition'] for r in json.loads((R/'research/bibliography.json').read_text())['references']}
expected={(r['key'],r['attribute_number'],r['new_name']):(r['new_module'],r['relation'],'' if r['relation']=='exact' else r['reason'],editions[r['key']]) for r in rows};env=dict(os.environ,LEAN_NUM_THREADS='1');search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,text=True).strip();env['LEAN_PATH']=os.pathsep.join(str((Path(p) if Path(p).is_absolute() else V/p).resolve()) for p in search.split(os.pathsep));lean=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=V,text=True).strip())/'bin/lean'
for i,modules in enumerate(groups):
 receipt=out/f'{i:03}.json'
 if receipt.exists():continue
 if time.monotonic()-start>440:break
 p=out/f'Probe{i:03}.lean';p.write_text('import SerrePositivity.Util.Citation\n'+'\n'.join('import '+m for m in modules)+'\n'+'\n'.join('#cite_tags '+key for key in keys)+'\n');t=time.monotonic();r=subprocess.run(['gtimeout','--kill-after=3s','75',str(lean),'--json',str(p)],cwd=V,env=env,text=True,capture_output=True);(out/f'{i:03}.log').write_text(r.stdout+r.stderr)
 if r.returncode:raise SystemExit(r.returncode)
 records=[]
 for line in r.stdout.splitlines():
  try:m=json.loads(line);record=json.loads(m['data'])
  except (ValueError,KeyError,TypeError):continue
  if isinstance(record,dict) and record.get('module','').startswith('SerrePositivity.'):records.append(record)
 receipt.write_text(json.dumps({'modules':modules,'seconds':time.monotonic()-t,'records':records},ensure_ascii=False));print('citation metadata group',i,len(records),round(time.monotonic()-t,2),flush=True)
if all((out/f'{i:03}.json').exists() for i in range(len(groups))):
 actual={};mismatches=[]
 for i in range(len(groups)):
  for r in json.loads((out/f'{i:03}.json').read_text())['records']:
   k=(r['key'],r['number'],r['declaration']);value=(r['module'],r['relation'],r['comment'],r['edition'])
   if k in actual and actual[k]!=value:mismatches.append({'key':k,'reason':'Imported records disagree'})
   actual[k]=value
   if not r['line'] or r['path']!=r['module'].replace('.','/')+'.lean':mismatches.append({'key':k,'reason':'Missing/incorrect actual source range'})
 missing=sorted(set(expected)-set(actual));extra=sorted(set(actual)-set(expected));different=[k for k in set(actual)&set(expected) if actual[k]!=expected[k]];summary={'expected':len(expected),'actual':len(actual),'missing':missing,'extra':extra,'different':different,'metadata_errors':mismatches,'groups':len(groups),'finished':time.time()};(W/'attribute-metadata-check.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('citation attributes',len(actual),'missing',len(missing),'extra',len(extra),'different',len(different),flush=True);raise SystemExit(bool(missing or extra or different or mismatches))
