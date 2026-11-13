import sys
from pathlib import Path
modules = sys.argv[1:]
template = Path('/tmp/bsw13-audit.lean').read_text()
start = template.index('open Lean in')
body = template[start:].splitlines()
i = next(i for i, line in enumerate(body) if 'let mods' in line)
body[i] = '  let mods : Array Name := #[' + ', '.join('`' + name for name in modules) + ']'
Path('/tmp/bsw13-c3-audit.lean').write_text('\n'.join('import ' + mod for mod in modules) + '\n\n' + '\n'.join(body) + '\n')
