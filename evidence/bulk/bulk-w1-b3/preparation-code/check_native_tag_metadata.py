from pathlib import Path
import json,subprocess,time,os
W=Path('/tmp/bulk-w1-b3');V=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');start=time.monotonic();plan=json.loads((W/'native-tag-plan.json').read_text());out=W/'native-tag-metadata';out.mkdir(exist_ok=True);lean=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=V,text=True).strip())/'bin/lean'
# Include the single existing tagged archive leaf without porting unrelated archives.
if not (W/'tag-archive-build.json').exists():
 targets=[p[:-5].replace('/','.') for p in json.loads((W/'native-tag-extra-files.json').read_text())]
 with (W/'tag-archive-build.log').open('w') as log:r=subprocess.run(['gtimeout','--kill-after=3s','150','lake','build',*targets],cwd=V,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 (W/'tag-archive-build.json').write_text(json.dumps({'targets':targets,'seconds':time.monotonic()-start}))
for side,root,field in [('before',W/'before','before_module'),('after',V,'after_module')]:
 env=dict(os.environ,LEAN_NUM_THREADS='1');paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);paths=[str((Path(p) if Path(p).is_absolute() else root/p).resolve()) for p in paths];env['LEAN_PATH']=os.pathsep.join(paths)
 if side=='before':assert str((W/'before/.lake/build/lib/lean').resolve()) in paths and str((V/'.lake/build/lib/lean').resolve()) not in paths
 owners=sorted({r[field] for r in plan});groups=[owners[i:i+64] for i in range(0,len(owners),64)]
 for i,modules in enumerate(groups):
  receipt=out/f'{side}-{i:03}.json'
  if receipt.exists():continue
  if time.monotonic()-start>440:raise SystemExit(0)
  p=out/f'{side}{i:03}.lean';p.write_text('import SerrePositivity.Util.Citation\n'+'\n'.join('import '+m for m in modules)+'\n#cite_tags Kerodon\n');t=time.monotonic();r=subprocess.run(['gtimeout','--kill-after=3s','75',str(lean),'--json',str(p)],cwd=root,env=env,text=True,capture_output=True);(out/f'{side}-{i:03}.log').write_text(r.stdout+r.stderr)
  if r.returncode:raise SystemExit(r.returncode)
  records=[]
  for line in r.stdout.splitlines():
   try:m=json.loads(line);record=json.loads(m['data'])
   except (ValueError,KeyError,TypeError):continue
   if isinstance(record,dict) and record.get('declaration','').startswith('SerrePositivity.'):records.append(record)
  receipt.write_text(json.dumps({'modules':modules,'records':records,'seconds':time.monotonic()-t},ensure_ascii=False));print('native tag group',side,i,len(records),flush=True)
checks={}
for side,namefield in [('before','before_name'),('after','after_name')]:
 expected={(r['tag'],r[namefield]) for r in plan};actual=set()
 for p in out.glob(side+'-*.json'):
  actual.update((r['number'],r['declaration']) for r in json.loads(p.read_text())['records'])
 checks[side]={'expected':len(expected),'actual':len(actual),'missing':sorted(expected-actual),'extra':sorted(actual-expected)}
(W/'native-tag-metadata-check.json').write_text(json.dumps(checks,indent=2));print('native tags',checks,flush=True);raise SystemExit(any(r['missing'] or r['extra'] for r in checks.values()))
