"""Reuse the unchanged KL checker, then check the new migration date explicitly."""
from pathlib import Path
import json,subprocess,time,os,hashlib,collections
W=Path('/tmp/bulk-w1-b3');V=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');out=W/'alias-check';out.mkdir(exist_ok=True);start=time.monotonic();BUDGET=int(os.environ.get('BULK_SLOT_SECONDS','1650'));rows=json.loads((W/'compatibility-final.json').read_text());groups=collections.defaultdict(list)
for row in rows:groups[row['module']].append(row)
expected=sorted((r['old'],r['new']) for r in rows);mapping=out/'all-aliases.json';mapping.write_text(json.dumps(rows));results=[]
for i,(module,aliases) in enumerate(sorted(groups.items())):
 receipt=out/f'{i:03}.receipt.json';source=V/(module.replace('.','/')+'.lean');signature=hashlib.sha256(source.read_bytes()).hexdigest()
 if receipt.exists() and json.loads(receipt.read_text()).get('source_sha256')==signature:continue
 if time.monotonic()-start>max(20,BUDGET-135):break
 inp=out/f'{i:03}.input.json';inp.write_text(json.dumps({'modules':[module],'aliases':aliases}));output=out/f'{i:03}.output.json';log=out/f'{i:03}.log';t=time.monotonic()
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s','90','lake','env','lean','--run',str(R/'scripts/refactor/check_deprecated_aliases.lean'),str(inp),str(output),str(mapping)],cwd=V,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode in [0,1] and output.exists(),(module,r.returncode,str(log))
 data=json.loads(output.read_text());assert data['checked']==len(aliases);assert sorted((r['old'],r['new']) for r in data['results'])==sorted((r['old'],r['new']) for r in aliases)
 unexpected=[row for row in data['results'] if row['errors']!=['deprecated date']]
 assert not unexpected,unexpected
 # Read the actual metadata; do not accept the old checker's date discrepancy alone.
 probe=out/f'Date{i:03}.lean';probe.write_text('import '+module+'\nopen Lean in\nrun_cmd do\n  let env ← getEnv\n'+''.join('  unless (Linter.deprecatedAttr.getParam? env '+json.dumps(row['old'])+'.toName).bind (·.since?) == some "2026-11-12" do throwError "incorrect bulk alias date"\n' for row in aliases))
 with (out/f'{i:03}.date.log').open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s','45','lake','env','lean',str(probe)],cwd=V,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode==0,('date probe',module,r.returncode)
 receipt.write_text(json.dumps({'module':module,'source_sha256':signature,'aliases':len(aliases),'checks':'unchanged KL checker: only expected old-date diagnostics; explicit date probe confirms 2026-11-12','seconds':time.monotonic()-t,'status':'PASS'}));print('alias group',i,len(aliases),'PASS',flush=True)
receipts=[json.loads(p.read_text()) for p in out.glob('*.receipt.json')]
if len(receipts)==len(groups):
 (W/'alias-check-complete.json').write_text(json.dumps({'aliases':sum(r['aliases'] for r in receipts),'wrappers':len(receipts),'expected_date':'2026-11-12','checker_source_sha256':hashlib.sha256((R/'scripts/refactor/check_deprecated_aliases.lean').read_bytes()).hexdigest(),'status':'PASS','finished':time.time()},indent=2))
