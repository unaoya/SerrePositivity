from pathlib import Path
import json,subprocess,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');B=W/'final-bundle';manifest=json.loads((B/'manifest.json').read_text());paths={m.replace('.','/')+'.lean' for m in manifest['files']};old=set(manifest['delete_paths']);allowed_einf={'SerrePositivity/EInfinity.lean',*('SerrePositivity/EInfinity/Perfectoidization/'+n+'.lean' for n in ['Comparison','Interface','DerivedCorollary','TheoryInterface'])};new_generic='SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/InitialValueCone.lean'
for path in paths|old:
 if path.startswith('SerrePositivity/AlgebraicGeometry/'):raise ValueError('protected AG file '+path)
 if path.startswith('SerrePositivity/InfinityCategories/') and path!=new_generic:raise ValueError('protected infinity file '+path)
 if (path.startswith('SerrePositivity/EInfinity/') or path=='SerrePositivity/EInfinity.lean') and path not in allowed_einf:raise ValueError('protected EInfinity file '+path)
for path in old:
 assert path not in paths,path
 p=A/path
 if p.exists():p.unlink()
for m,sha in manifest['files'].items():
 p=B/(m.replace('.','/')+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
 target=A/p.relative_to(B);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes())
(A/'scripts/refactor/layers.json').write_bytes((B/'scripts/refactor/layers.json').read_bytes())
subprocess.run(['git','add','-A','--','SerrePositivity','SerrePositivity.lean','scripts/refactor/layers.json'],cwd=A,check=True)
changed=subprocess.check_output(['git','diff','--cached','--name-only'],cwd=A,text=True).splitlines();assert set(changed)<=paths|old|{'scripts/refactor/layers.json'},set(changed)-(paths|old|{'scripts/refactor/layers.json'})
receipt={'scope':'isolated preview only; actual bulk/b3prime Lean not changed; no freeze notification issued','bundle_manifest_sha256':hashlib.sha256((B/'manifest.json').read_bytes()).hexdigest(),'tracked_changed_paths':changed,'new_or_retained_module_files':len(paths),'deleted_paths':len(old)};(W/'preview-install-receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2));print('isolated preview installed',len(changed),'tracked changed paths')
