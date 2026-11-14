from pathlib import Path
import subprocess,time,json,datetime,hashlib
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');index=len(list(w.glob('preservation-slot-*.log')))
receipt=json.load(open('/tmp/bulk-w1-b2/private-snapshot/receipt.json'))
assert hashlib.sha256((r/'scripts/refactor/decl_snapshot.lean').read_bytes()).hexdigest()==receipt['original_source_sha256']
assert hashlib.sha256(Path('/tmp/bulk-w1-b2/private-snapshot/Snapshot.lean').read_bytes()).hexdigest()==receipt['verification_source_sha256']
assert hashlib.sha256(Path('/tmp/bulk-w1-b2/private-snapshot/snapshot').read_bytes()).hexdigest()==receipt['binary_sha256']
assert (w/'target-build-complete.json').exists() and (w/'moved-audits-complete.json').exists()
assert not json.load(open(w/'owned-private-rules-summary.json'))['missing_private_source_bindings']
while not (w/'preservation-complete.json').exists():
 if 8<=datetime.datetime.now().hour<23:raise SystemExit('Night preservation paused at daytime boundary')
 if (w/'preservation-errors.json').exists():raise SystemExit('Review saved differences without weakening checks')
 log=w/f'preservation-slot-{index:03}.log';resource=w/f'preservation-slot-{index:03}.resources.json'
 with resource.open('w') as f:p=subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--night-only','--seconds','1780','--','python3','-B',str(w/'preserve_slot.py')],stdout=f)
 print('preservation slot',index,'rc',p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 index+=1
