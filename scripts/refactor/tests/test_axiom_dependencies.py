#!/usr/bin/env python3
"""Exercise complete axiom traversal on a cyclic inductive and an added axiom."""
import argparse,json,os,shutil,subprocess,tempfile
from pathlib import Path

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--checker',default='scripts/refactor/check_deprecated_aliases.lean');args=parser.parse_args();checker=Path(args.checker).resolve()
 actual=dict(line.split('=',1) for line in subprocess.check_output(['lake','env'],text=True).splitlines() if '=' in line);env={**os.environ,**actual};lean=shutil.which('lean',path=env['PATH']);assert lean
 with tempfile.TemporaryDirectory(prefix='if-f2-axiom-test-') as tmp:
  root=Path(tmp).resolve();src=root/'AxiomCycleFixture.lean';src.write_text('''import Lean
namespace AxiomCycleFixture
axiom first : True
axiom extra : True
inductive Base : Prop where
  | plain : Base
  | linked : (first = first) → Base
inductive Extended : Prop where
  | plain : Extended
  | prior : Base → Extended
  | added : (extra = extra) → Extended
end AxiomCycleFixture
''')
  subprocess.run([lean,'--root='+str(root),'-o',str(root/'AxiomCycleFixture.olean'),str(src)],env=env,check=True)
  inp=root/'input.json';out=root/'output.json';inp.write_text(json.dumps(dict(modules=['AxiomCycleFixture'],pairs=[dict(old='AxiomCycleFixture.Base.plain',new='AxiomCycleFixture.Base.linked'),dict(old='AxiomCycleFixture.Base.plain',new='AxiomCycleFixture.Extended.plain')])))
  env['LEAN_PATH']=str(root)+os.pathsep+env.get('LEAN_PATH','');subprocess.run([lean,'--root='+str(checker.parent), '--run',str(checker),'--axioms',str(inp),str(out)],env=env,check=True)
  rows=json.loads(out.read_text())
  for row in rows:
   for key in ['old','new']:assert row[key]['missing']==[],row
  assert rows[0]['old']['axioms']==rows[0]['new']['axioms']==['AxiomCycleFixture.first'],rows[0]
  assert rows[1]['old']['axioms']==['AxiomCycleFixture.first'],rows[1]
  assert rows[1]['new']['axioms']==['AxiomCycleFixture.extra','AxiomCycleFixture.first'],rows[1]
  print('PASS: cyclic constructors retain their dependency; an additional axiom is detected')
if __name__=='__main__':main()
