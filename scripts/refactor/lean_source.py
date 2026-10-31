"""概要：分割・対象検査で共有する保守的な Lean コマンド抽出。
方針：元の文字列の範囲だけを切り出す。規約：未対応の構文は位置付きで拒否する。
使われ方：parse_source / render / dependencies を split_module と validate_targets が使う。
"""
from dataclasses import dataclass, field
import re

from layer_check import code_only, imports

NAME = r"[\w\u0080-\uffff'][\w\u0080-\uffff'.]*"
DECL = re.compile(r'^(?P<mods>(?:(?:private|public|protected|noncomputable|unsafe|local|scoped)\s+)*)'
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
    namespace: str = ''
    attribute_spec: str = ''
    attribute_targets: tuple = ()


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


def parse_source(text, label='<source>', snapshot=None, module=None):
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
        if not core or re.match(r'^(include|omit|open|set_option|variable)\b.*\bin\s*$', core):
            if pending is None: pending = doc_start(text, offset)
            offset += len(raw); continue
        while re.match(r'^(open|set_option|variable|include|omit)\b.*?\bin\s+', core):
            core = re.sub(r'^(open|set_option|variable|include|omit)\b.*?\bin\s+', '', core, count=1)
        kind = 'decl' if DECL.match(core) else None
        if kind is None:
            if re.match(r'^(?:public\s+|meta\s+|private\s+)*import\b|^(module|prelude)\b', core): kind = 'header'
            elif re.match(r'^(?:noncomputable\s+|public\s+)*section\b|^namespace\b', core): kind = 'scope'
            elif re.match(r'^end(?:\s|$)', core): kind = 'end'
            elif re.match(r'^(universe|universes|open|variable|set_option|include|omit)\b', core): kind = 'context'
            elif core.startswith('attribute '): kind = 'attribute'
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
        command = Command(start, end, kind, text[start:end], context=tuple(active), namespace=namespace)
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
            active.append(i)
        elif kind == 'attribute':
            match = re.fullmatch(r'attribute\s+\[([^]\n]+)\]\s+(.+?)\s*', code_only(command.text).strip())
            if not match or not all(re.fullmatch(NAME, n) for n in match[2].split()):
                raise Unsupported(f'{label}: unsupported attribute command: {core}')
            if ',' in match[1]:
                raise Unsupported(f'{label}: multiple attribute specifications require manual review')
            command.attribute_spec = match[1]
            command.attribute_targets = tuple(match[2].split())
        else:
            match = DECL.match(core)
            rest = core[match.end():]
            if match['kind'] == 'instance' and rest.startswith('(priority'):
                close = rest.find(')')
                if close < 0: raise Unsupported(f'{label}: multiline instance priority')
                rest = rest[close+1:].lstrip()
            named = re.match(NAME, rest)
            short = named[0] if named else None
            full = (short.removeprefix('_root_.') if short and short.startswith('_root_.') else
                    '.'.join(filter(None, [namespace, short])) if short else None)
            if snapshot is not None:
                if module is None:
                    matching = [x['module'] for x in snapshot.get('sources', []) if x['source'] == text]
                    if len(matching) != 1: raise Unsupported(f'{label}: snapshot source/module is ambiguous')
                    module = matching[0]
                first = text.count('\n', 0, start) + 1
                last = text.count('\n', 0, end-1) + 1
                candidates = [row for row in snapshot['declarations'] if row.get('module') == module
                              and row.get('source_range') and
                              first <= row['source_range']['selection_start_line'] <= last]
                names = {row['name'] for row in candidates}
                primary = [row for row in candidates if row.get('environment_parent') not in names]
                if full is not None:
                    if candidates and full not in names:
                        raise Unsupported(f'{label}: declaration name disagrees with source position: {full}')
                elif match['kind'] == 'instance' and len(primary) == 1:
                    full = primary[0]['name']
                elif full is None:
                    raise Unsupported(f'{label}: anonymous instance requires one declaration at source position {first}:{last}')
            if full is None:
                raise Unsupported(f'{label}: declaration requires an explicit name or positioned snapshot: {core}')
            if full in declarations: raise Unsupported(f'{label}: duplicate declaration {full}')
            command.name, command.public = full, 'private' not in match['mods'].split()
            declarations[full] = i
        commands.append(command)
    if any(part for _,part,_,_ in scopes): raise Unsupported(f'{label}: unclosed named namespace/section')
    source = Source(text, commands, declarations)
    # Resolve local attribute targets, including generated fields, via lexical namespaces.
    for c in commands:
        if c.kind != 'attribute': continue
        targets = []
        for name in c.attribute_targets:
            spaces = c.namespace.split('.') if c.namespace else []
            candidates = ([name.removeprefix('_root_.')] if name.startswith('_root_.') else
                          ['.'.join(spaces[:i] + [name]) for i in range(len(spaces), -1, -1)])
            parent = next((owner(n, declarations) for n in candidates if owner(n, declarations)), None)
            if parent:
                declaration = commands[declarations[parent]]
                scopes_at = lambda x: [j for j in x.context if commands[j].kind == 'scope']
                if scopes_at(c) != scopes_at(declaration):
                    raise Unsupported(f'{label}: attribute and target have different scopes: {name}')
                if declarations[parent] >= commands.index(c):
                    raise Unsupported(f'{label}: attribute precedes target: {name}')
            targets.append((name, parent))
        c.attribute_targets = tuple(targets)
    return source


def check_attribute_dependencies(source, moved):
    for i,c in enumerate(source.commands):
        if c.kind != 'attribute': continue
        local = bool(re.search(r'\b(local|scoped)\b', c.attribute_spec))
        if local or all(parent for _,parent in c.attribute_targets): continue
        # Any moved declaration elaborated under this global mutation may rely on
        # it through typeclass search, simp, reducibility, or another attribute.
        for name in moved:
            j = source.declarations[name]
            if j > i:
                raise Unsupported('moved declaration may depend on external global attribute: '+c.text.strip())


def render(source, selected, *, side='keep'):
    wanted = {i for i,c in enumerate(source.commands) if c.kind == 'header'}
    for name in selected:
        i = source.declarations[name]; wanted.add(i); wanted.update(source.commands[i].context)
    attached, external = {}, {}
    for i,c in enumerate(source.commands):
        if c.kind != 'attribute': continue
        for name,parent in c.attribute_targets:
            fragment = 'attribute ['+c.attribute_spec+'] '+name+'\n'
            if parent in selected:
                attached.setdefault(source.declarations[parent], []).append(fragment)
            elif parent is None and (side == 'keep' or re.search(r'\b(local|scoped)\b', c.attribute_spec)):
                external.setdefault(i, []).append(fragment)
                wanted.add(i);wanted.update(c.context)
    for i,c in enumerate(source.commands):
        if c.kind == 'end' and c.closes in wanted: wanted.add(i)
    return ''.join((''.join(external.get(i, [])) if c.kind == 'attribute' else c.text) +
                   ''.join(attached.get(i, [])) for i,c in enumerate(source.commands) if i in wanted)


def owner(name, declarations):
    # Explicit source names take precedence over generated projections/reassoc lemmas.
    if name in declarations: return name
    candidates = [n for n in declarations if name.startswith(n+'.')]
    return max(candidates, key=len) if candidates else None


def transient_names(snapshot):
    """External parents are resolved by Lean's environment, never guessed from spelling.

    Explicit source declarations take precedence. The lexical check also handles source
    syntax outside the conservative splitter; ambiguity keeps a row in the comparison.
    """
    sources = {r['module']: r['source'] for r in snapshot.get('sources', [])}
    result = set()
    exact_names = {}
    for module, text in sources.items():
        try: exact_names[module] = set(parse_source(text, snapshot=snapshot, module=module).declarations)
        except Unsupported: pass
    for row in snapshot['declarations']:
        parent = row.get('environment_parent')
        parent_module = row.get('parent_module')
        if not parent or not parent_module or parent_module == row.get('module'): continue
        text = sources.get(row.get('module'))
        if text is None: raise Unsupported('source required to classify generated declaration: '+row['name'])
        if row['module'] in exact_names:
            names=exact_names[row['module']]
            if declaration_owner(row,names,{r['name']:r for r in snapshot['declarations']}): continue
        else:
            declared = re.findall(r'\b(?:def|abbrev|theorem|lemma|opaque|axiom|structure|class|inductive|instance)\s+('+NAME+r')', code_only(text))
            if any(row['name'] == n.removeprefix('_root_.') or row['name'].endswith('.'+n) for n in declared): continue
        result.add(row['name'])
    return sorted(result)


GENERATED_SUFFIXES = ('assoc', 'apply', 'symm_apply', 'fst', 'snd', 'coe', 'hom', 'inv', 'inj', 'injEq')


def normalized_private_name(name):
    return re.sub(r'^_private\..*?\.\d+\.', '', name)


def declaration_owner(row, source_names, rows):
    """§10.11: exact source, position, normalized prefix, then approved suffix."""
    name = normalized_private_name(row['name'])
    if name in source_names: return name
    position = row.get('source_range')
    if position:
        matches = [n for n in source_names if n in rows and
                   rows[n].get('module') == row.get('module') and rows[n].get('source_range') and
                   rows[n]['source_range']['start_line'] <= position['start_line'] <=
                   rows[n]['source_range']['end_line']]
        if len(matches) > 1: raise Unsupported('ambiguous generated declaration position: '+name)
        if matches: return matches[0]
    # Source declarations and snapshot rows are environment declarations too.
    normalized_rows = {normalized_private_name(n): r for n,r in rows.items()}
    prefixes = [n for n in normalized_rows.keys() | set(source_names) if name.startswith(n+'.')]
    parent = normalized_private_name(row.get('environment_parent') or '')
    if parent: prefixes.append(parent)
    parent = max(prefixes,key=len) if prefixes else None
    visited = {name}
    while parent and parent not in visited:
        if parent in source_names and (parent not in normalized_rows or
                normalized_rows[parent].get('module') == row.get('module')): return parent
        visited.add(parent)
        ancestor = normalized_rows.get(parent, {})
        parent = normalized_private_name(ancestor.get('environment_parent') or '')
    suffix_parents = set()
    for suffix in GENERATED_SUFFIXES:
        if name.endswith('_'+suffix):
            parent = name[:-len(suffix)-1]
            if parent in source_names and (parent not in rows or rows[parent].get('module') == row.get('module')):
                suffix_parents.add(parent)
    if len(suffix_parents) > 1:
        raise Unsupported('ambiguous generated declaration suffix: '+name)
    return next(iter(suffix_parents)) if suffix_parents else None


def dependency_directions(source, moved, snapshot):
    source_names = set(source.declarations)
    rows = snapshot['declarations']
    missing = source_names - {r['name'] for r in rows}
    if missing: raise Unsupported('snapshot lacks declarations (private/anonymous syntax needs review): '+', '.join(sorted(missing)))
    moved_to_keep, keep_to_moved = set(), set()
    transient = set(transient_names(snapshot))
    by_name = {r['name']: r for r in rows}
    for row in rows:
        if row['name'] in transient: continue
        src = declaration_owner(row, source_names, by_name)
        if src is None: raise Unsupported('cannot associate generated declaration: ' + row['name'])
        for used in row['used_constants']:
            dst = declaration_owner(by_name[used],source_names,by_name) if used in by_name else owner(used, source_names)
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
