"""生成スクリプトの共通部分：宣言の完全な名前の解決と、Verso の本文のエスケープ。"""
import re, os, collections
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|scoped|local|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
SEC = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|public\s+)*section(?:\s+(\S+))?\s*$')
END = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'₀-₉!?]*$")
class Resolver:
    def __init__(self, paths):
        self.index = collections.defaultdict(list)
        for p in paths:
            fp = p if p.startswith('SerrePositivity/') else '.lake/packages/mathlib/' + p
            if os.path.exists(fp): self._scan(fp, p[:-5].replace('/', '.'))
        self.by_suffix = collections.defaultdict(set)
        for full in self.index:
            parts = full.split('.')
            for k in range(len(parts)): self.by_suffix['.'.join(parts[k:])].add(full)
    def _scan(self, path, mod):
        stack = []
        for l in open(path, encoding='utf-8', errors='ignore'):
            if (m := NS.match(l)): stack.append(m.group(1).split('.')); continue
            if SEC.match(l): stack.append([]); continue
            if END.match(l) and stack: stack.pop(); continue
            if (m := DECL.match(l)):
                n = m.group(2)
                full = n[7:] if n.startswith('_root_.') else '.'.join([p for ps in stack for p in ps] + [n])
                self.index[full].append(mod)
    def resolve(self, entry):
        """「名前 @ パス:行」を（完全な名前, モジュール）に。一意でなければ None。"""
        if ' @ ' not in entry: return None
        name = entry.split(' @ ', 1)[0].split('（')[0].split(' (')[0].strip()
        if not IDENT.match(name): return None
        c = self.by_suffix.get(name, set())
        if len(c) != 1: return None
        full = next(iter(c)); return full, self.index[full][0]
def paths_of(cells):
    out = set()
    for cell in cells:
        for e in cell.split(' | '):
            if ' @ ' in e: out.add(e.split(' @ ', 1)[1].rsplit(':', 1)[0].strip())
    return out
def esc(s):
    return re.sub(r'([\\*_`\[\]{}#$<>|~^])', r'\\\1', s)
