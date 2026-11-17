from pathlib import Path
import json,gzip,re
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=r/'evidence/bulk/bulk-w1-b2/final'
plan=json.load(gzip.open(d/'namespace-map.json.gz','rt'));old='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence';new=plan['modules'][old];plan['modules'][old]=old
for row in plan['rows']:
 if row.get('new_module')==new:row['new_module']=old
for table in plan.get('declarations',{}).values():
 for k,v in list(table.items()):
  if v==new:table[k]=old
(w/'namespace-map.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2));(w/'module-map.json').write_text(json.dumps(plan['modules'],indent=2))
p=w/'rendered/scripts/audit_derived_infinity.lean';s=p.read_text();count=0
def merge(m):
 global count
 a,b=m[1],m[2];lines=[line for line in (a+b).splitlines() if line.strip()]
 assert all(line.startswith('import ') or line.startswith('public import ') for line in lines)
 seen=set();result=[]
 for line in lines:
  pre,module=line.rsplit(' ',1);module=plan['modules'].get(module,module);line=pre+' '+module
  if line not in seen:seen.add(line);result.append(line)
 count+=1;return '\n'.join(result)+'\n'
s=re.sub(r'(?ms)^<<<<<<<[^\n]*\n(.*?)^=======\n(.*?)^>>>>>>>[^\n]*\n',merge,s);assert count==1 and '<<<<<<<' not in s;p.write_text(s)
summary=json.load(open(w/'rebase-summary.json'));summary['resolved_conflicts']=[{'path':str(p.relative_to(w/'rendered')),'policy':'Union both import blocks, rename exact modules, retain all frozen-main imports'}];summary['conflicts']=[];(w/'rebase-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2))
print('plan prepared, IntegralExistence retained; import conflict resolved without changing declarations')
