from pathlib import Path
import json,hashlib,ast
w=Path('/tmp/bulk-w1-b2');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');v=w/'preview';plan=json.load(open(w/'preservation-module-plan.json'));mm=plan['modules'];gs=json.load(open(w/'preservation-groups.json'));splits=json.load(open(w/'preservation/splits.json'));allold=[m for g in gs for m in g];targets=sorted({mm.get(m,m) for m in allold}|{d for m in allold for d in plan.get('declarations',{}).get(m,{}).values()});globalhash=hashlib.sha256(json.dumps({m:hashlib.sha256((v/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in targets},sort_keys=True).encode()).hexdigest();ctx=dict(W=w,R=r,V=v,plan=plan,mm=mm,globalhash=globalhash,hashlib=hashlib,json=json,binary_hash=hashlib.sha256((w/'private-snapshot/snapshot').read_bytes()).hexdigest(),module_plan_hash=hashlib.sha256((w/'preservation-module-plan.json').read_bytes()).hexdigest());node=next(n for n in ast.parse((w/'make_declaration_table.py').read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='expected_signature');exec(compile(ast.Module(body=[node],type_ignores=[]),'<actual full signature>','exec'),ctx)
passed=[];missing=[]
def check(ms,label):
 if label in splits:
  n=len(ms)//2;check(ms[:n],label+'a');check(ms[n:],label+'b');return
 p=w/'preservation'/(label+'.receipt.json')
 if p.exists():
  d=json.load(open(p))
  if d.get('comparison_rc')==0 and d.get('status')=='PASS' and d.get('signature')==ctx['expected_signature'](ms):passed.extend(ms);return
 missing.append({'group':label,'modules':ms})
for i,ms in enumerate(gs):check(ms,f'{i:04}')
print(json.dumps({'passed_with_current_full_signature':len(passed),'remaining':len(allold)-len(passed),'missing':missing},ensure_ascii=False))
