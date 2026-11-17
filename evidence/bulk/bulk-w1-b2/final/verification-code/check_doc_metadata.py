from pathlib import Path
import subprocess,json,os,time
w=Path('/tmp/bulk-w1-b2');root=w/'replay-tree';out=w/'bounded-doc-check';plan=json.load(open(w/'bounded-doc-supplement-plan.json'));modules={r['module'] for r in plan['rows']};rows=[r for r in json.load(open(w/'attribute-declaration-final.json')) if r['action']=='attach' and r['new_module'] in modules];keys=sorted({r['key'] for r in rows});expected={(r['key'],r['attribute_number'],r['new_name']) for r in rows};owners=sorted({r['new_module'] for r in rows});p=out/'Metadata.lean';p.write_text('import SerrePositivity.Util.Citation\n'+'\n'.join('import '+m for m in owners)+'\n'+'\n'.join('#cite_tags '+key for key in keys)+'\n');paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);env=dict(os.environ,LEAN_NUM_THREADS='2',LEAN_PATH=os.pathsep.join(str((Path(x) if Path(x).is_absolute() else root/x).resolve()) for x in paths));lean=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip())/'bin/lean';t=time.monotonic();s=subprocess.run(['gtimeout','--kill-after=3s','60',str(lean),'--json',str(p)],cwd=root,env=env,text=True,capture_output=True);(out/'metadata.log').write_text(s.stdout+s.stderr);assert s.returncode==0;records=[]
for line in s.stdout.splitlines():
 try:rec=json.loads(json.loads(line)['data'])
 except (ValueError,KeyError,TypeError):continue
 if isinstance(rec,dict) and rec.get('module') in modules:records.append(rec)
actual={(r['key'],r['number'],r['declaration']) for r in records};assert expected==actual,(expected-actual,actual-expected)
for r in records:
 assert r['path']==r['module'].replace('.','/')+'.lean';assert 0<r['line']<=len((root/r['path']).read_text().splitlines())
result={'status':'PASS','expected':len(expected),'actual':len(actual),'metadata_errors':0,'seconds':time.monotonic()-t,'records':records};(out/'metadata.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('doc supplement citation metadata',len(actual))
