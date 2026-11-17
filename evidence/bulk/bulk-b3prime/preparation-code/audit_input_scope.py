from pathlib import Path
import json,hashlib,subprocess
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
PATHS=['SerrePositivity','SerrePositivity.lean','scripts/refactor','lakefile.toml','lake-manifest.json','lean-toolchain','research/bibliography.json']
def inputs(application):
 audits=set(json.loads((W/'all-audit-inventory.json').read_text())['audits'])
 assert not subprocess.check_output(['git','diff','HEAD','--name-only','--',*PATHS],cwd=R,text=True).strip(),'uncommitted library/config/helper changes'
 assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','SerrePositivity','scripts/refactor'],cwd=R,text=True).strip(),'untracked library/helper changes'
 trees={p:subprocess.check_output(['git','rev-parse','HEAD:'+p],cwd=R,text=True).strip() for p in PATHS}
 material={'tracked_library_and_tooling_trees':trees,'applied_non_audit_sources':{p:h for p,h in application['paths_written'].items() if p not in audits}}
 return material,hashlib.sha256(json.dumps(material,sort_keys=True).encode()).hexdigest()
