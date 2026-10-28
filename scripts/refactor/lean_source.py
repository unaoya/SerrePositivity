"""概要：分割・対象検査で共有する保守的な Lean コマンド抽出。
方針：元の文字列の範囲だけを切り出す。規約：未対応の構文は位置付きで拒否する。
使われ方：parse_source / render / dependencies を split_module と validate_targets が使う。
"""
from dataclasses import dataclass, field
import re

from layer_check import code_only, imports

NAME = r"[\w\u0080-\uffff'][\w\u0080-\uffff'.]*"
DECL = re.compile(r'^(?P<mods>(?:(?:private|public|protected|noncomputable|unsafe)\s+)*)'
                  r'(?P<kind>def|abbrev|theorem|lemma|opaque|axiom|structure|class|inductive|instance)\b\s*')


class Unsupported(ValueError): pass


def read_source(path):
    return path.read_bytes().decode('utf-8')


def write_source(path, text):
    path.write_bytes(text.encode('utf-8'))


@dataclass
class Command:
    start: int
    end: int
    kind: str
    text: str
    name: str = ''
    public: bool = True
    context: tuple = ()
    closes: int | None = None


@dataclass
class Source:
    text: str
    commands: list[Command]
    declarations: dict[str, int] = field(default_factory=dict)


def strip_attributes(text):
    while text.startswith('@['):
        depth, end = 1, 2
        while end < len(text) and depth:
            depth += (text[end] == '[') - (text[end] == ']'); end += 1
        if depth: raise Unsupported('multiline attribute syntax requires manual review')
        text = text[end:].lstrip()
    return text


def doc_start(text, position):
    """Attach the immediately preceding docstring, including nested comments."""
    start = text.rfind('/--', 0, position)
    if start < 0: return position
    i, depth = start + 2, 1
    while i < position and depth:
        if text.startswith('/-', i): depth += 1; i += 2
        elif text.startswith('-/', i): depth -= 1; i += 2
        else: i += 1
    return start if depth == 0 and not text[i:position].strip() else position


def parse_source(text, label='<source>'):
    mask = code_only(text)
    boundaries, pending = [], None
    offset = 0
    for raw in mask.splitlines(keepends=True):
        line = raw.rstrip('\r\n')
        if not line.strip(): offset += len(raw); continue
        if line[0].isspace():
            # An indented declaration must never be swallowed into a namespace,
            # variable command, or preceding declaration and copied to both sides.
            stripped = strip_attributes(line.lstrip())
            command = DECL.match(stripped) or re.match(
                r'^(?:(?:public|private|noncomputable|meta)\s+)*(?:namespace|section|end|import|module|'
                r'prelude|variable|universe|universes|open|set_option|mutual|attribute|include|omit)\b', stripped)
            if command or line.lstrip().startswith('@['):
                raise Unsupported(f'{label}:{text.count(chr(10),0,offset)+1}: indented command requires manual review: {line.strip()}')
            offset += len(raw); continue
        try: core = strip_attributes(line)
        except Unsupported as exc: raise Unsupported(f'{label}:{text.count(chr(10),0,offset)+1}: {exc}') from exc
        # Attributes and one-command scope wrappers belong to the following declaration.
        if not core or re.match(r'^(include|omit|open|set_option)\b.*\bin\s*$', core):
            if pending is None: pending = doc_start(text, offset)
            offset += len(raw); continue
        kind = 'decl' if DECL.match(core) else None
        if kind is None:
            if re.match(r'^(?:public\s+|meta\s+|private\s+)*import\b|^(module|prelude)\b', core): kind = 'header'
            elif re.match(r'^(?:noncomputable\s+|public\s+)*section\b|^namespace\b', core): kind = 'scope'
            elif re.match(r'^end(?:\s|$)', core): kind = 'end'
            elif re.match(r'^(universe|universes|open|variable|set_option)\b', core): kind = 'context'
            else:
                raise Unsupported(f'{label}:{text.count(chr(10),0,offset)+1}: unsupported top-level syntax: {line}')
        if pending is not None and kind not in ('decl', 'scope'):
            raise Unsupported(f'{label}: unattached attribute/local scope before {line}')
        start = pending if pending is not None else doc_start(text, offset)
        boundaries.append((start, kind, core)); pending = None
        offset += len(raw)
    if pending is not None: raise Unsupported(f'{label}: dangling declaration prefix')
    if not boundaries: raise Unsupported(f'{label}: no top-level commands')
    boundaries[0] = (0, boundaries[0][1], boundaries[0][2])
    commands, declarations = [], {}
    active, scopes, namespace = [], [], ''
    for i, (start, kind, core) in enumerate(boundaries):
        end = boundaries[i+1][0] if i+1<len(boundaries) else len(text)
        command = Command(start, end, kind, text[start:end], context=tuple(active))
        if kind == 'scope':
            is_namespace = core.startswith('namespace ')
            if is_namespace:
                part = core.split()[1]
                if not re.fullmatch(NAME, part): raise Unsupported(f'{label}: unsupported namespace')
            else:
                part = core.split('section',1)[1].strip()
                if part and not re.fullmatch(NAME, part): raise Unsupported(f'{label}: unsupported section')
            scopes.append((i, part, list(active), namespace))
            if is_namespace: namespace = '.'.join(filter(None, [namespace, part])).removeprefix('_root_.')
            active.append(i)
        elif kind == 'end':
            if not scopes: raise Unsupported(f'{label}: unmatched end')
            opener, part, old_active, old_namespace = scopes.pop()
            end_name = core[3:].strip()
            if end_name and end_name != part and not part.endswith('.'+end_name):
                raise Unsupported(f'{label}: mismatched end {end_name}')
            command.closes = opener; active, namespace = old_active, old_namespace
        elif kind in ('header', 'context'):
            if kind == 'header' and declarations: raise Unsupported(f'{label}: header after declarations')
            if core.startswith('variable') and re.search(r'\bin\b', code_only(command.text)):
                raise Unsupported(f'{label}: variable ... in is not supported')
            active.append(i)
        else:
            match = DECL.match(core)
            rest = core[match.end():]
            if match['kind'] == 'instance' and rest.startswith('(priority'):
                close = rest.find(')')
                if close < 0: raise Unsupported(f'{label}: multiline instance priority')
                rest = rest[close+1:].lstrip()
            named = re.match(NAME, rest)
            if not named: raise Unsupported(f'{label}: declaration requires an explicit name: {core}')
            short = named[0]
            if short.startswith('_root_.'): full = short.removeprefix('_root_.')
            else: full = '.'.join(filter(None, [namespace, short]))
            if full in declarations: raise Unsupported(f'{label}: duplicate declaration {full}')
            command.name, command.public = full, 'private' not in match['mods'].split()
            declarations[full] = i
        commands.append(command)
    if any(part for _,part,_,_ in scopes): raise Unsupported(f'{label}: unclosed named namespace/section')
    return Source(text, commands, declarations)


def render(source, selected):
    wanted = {i for i,c in enumerate(source.commands) if c.kind == 'header'}
    for name in selected:
        i = source.declarations[name]; wanted.add(i); wanted.update(source.commands[i].context)
    for i,c in enumerate(source.commands):
        if c.kind == 'end' and c.closes in wanted: wanted.add(i)
    return ''.join(c.text for i,c in enumerate(source.commands) if i in wanted)


def owner(name, declarations):
    # Explicit source names take precedence over generated projections/reassoc lemmas.
    if name in declarations: return name
    candidates = [n for n in declarations if name.startswith(n+'.') or name.startswith(n+'_')]
    return max(candidates, key=len) if candidates else None


def dependency_directions(source, moved, snapshot):
    source_names = set(source.declarations)
    rows = snapshot['declarations']
    missing = source_names - {r['name'] for r in rows}
    if missing: raise Unsupported('snapshot lacks declarations (private/anonymous syntax needs review): '+', '.join(sorted(missing)))
    moved_to_keep, keep_to_moved = set(), set()
    for row in rows:
        src = owner(row['name'], source_names)
        if src is None: raise Unsupported('cannot associate generated declaration: ' + row['name'])
        for used in row['used_constants']:
            dst = owner(used, source_names)
            if dst is None or src == dst: continue
            if src in moved and dst not in moved: moved_to_keep.add((src,dst))
            elif src not in moved and dst in moved: keep_to_moved.add((src,dst))
    return sorted(moved_to_keep), sorted(keep_to_moved)


def uses_names(text, names):
    tokens = set(re.findall(NAME, code_only(text)))
    for name in names:
        parts = name.split('.')
        for i in range(len(parts)):
            suffix = '.'.join(parts[i:])
            if any(t == suffix or t.startswith(suffix+'.') or t.startswith(suffix+'_') for t in tokens): return True
    return False


def add_import(text, module):
    if module in imports(text): return text
    # Insert immediately after the module header, preserving every existing byte.
    mask = code_only(text)
    match = re.search(r'(?m)^module\s*\n', mask)
    position = match.end() if match else 0
    command = ('public import ' if match else 'import ') + module + ('\r\n' if '\r\n' in text else '\n')
    return text[:position]+command+text[position:]
