"""Certify unchanged individual audit inputs after the single reserved-binder fix.
Original execution receipts are never modified. Use the archived pre-fix input
inventory; completed audits on the new input need no legacy certification.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,re,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--results',type=Path,required=True);p.add_argument('--fix',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();load=lambda p:json.loads(gzip.open(p,'rt').read() if p.suffix=='.gz' else p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();base=load(a.before);old=base['input_sha256'];current={p:sha(root/p) for p in old};changed=[p for p in old if old[p]!=current[p]];assert changed==['scripts/audit_einfinity.lean'],changed;fix=load(a.fix);assert fix['path']==changed[0] and old[changed[0]]==fix['before_sha256'] and current[changed[0]]==fix['after_sha256'];signature=hashlib.sha256(json.dumps(current,sort_keys=True).encode()).hexdigest();sys.path.insert(0,str(root/'scripts/refactor'));from audit_imports import audit_imports;from layer_check import code_only
valid={};rerun=[]
for p in sorted(a.results.glob('[0-9][0-9][0-9].json')):
 r=load(p)
 if r['signature']!=base['signature']:continue
 path=r['path'];assert r['returncode']==0 and r['source_sha256']==old[path]==current[path]
 source=(root/path).read_text();imports=audit_imports(source);safe_imports=all(m.split('.')[0] in ['SerrePositivity','Lean','Std','Mathlib','Batteries','Aesop','Qq','ProofWidgets','Plausible','Init'] for m in imports);file_reads=bool(re.search(r'\b(?:IO\.FS|readFile|readBinFile|readDir|walkDir)\b',code_only(source)))
 if not safe_imports or file_reads:rerun.append(dict(path=path,imports=sorted(imports),file_reads=file_reads));continue
 valid[path]=dict(receipt=str(p),receipt_sha256=sha(p),source_sha256=current[path],legacy_signature=r['signature'],imports=sorted(imports))
d=dict(current_signature=signature,legacy_signature=base['signature'],changed_inputs=changed,changed_input_sha256={p:dict(before=old[p],after=current[p]) for p in changed},common_inputs_unchanged=True,valid_legacy_receipts=valid,rerun=rerun,old_input_hashes_sha256=hashlib.sha256(json.dumps(old,sort_keys=True).encode()).hexdigest(),policy='B3-style independent audit input equivalence: common library/config/bibliography/core helpers and each retained audit unchanged; locked or unchanged imports, no direct file reads. Raw execution receipts remain original. Normal full verify must run all 106 audits with cache disabled.');a.output.write_text(json.dumps(d,indent=2)+'\n');print('certified',len(valid),'rerun',len(rerun))
