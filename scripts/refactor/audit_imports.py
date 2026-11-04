"""Collect audit dependencies without executing Lean (including literal importModules)."""
import re
from layer_check import code_only

NAME = r"[\w\u0080-\uffff']+(?:\.[\w\u0080-\uffff']+)*"

def _array_end(clean, start):
    depth = 0
    for i in range(start, len(clean)):
        if clean[i] == '[': depth += 1
        elif clean[i] == ']':
            depth -= 1
            if depth == 0: return i
    raise ValueError('unterminated importModules array literal')


def audit_imports(source):
    """Return static and runtime imports; reject unsupported runtime dependencies.

    importModules must take an array literal of Import records with literal module
    Names. Silently skipping computed arrays would reproduce a clean-build hole.
    Comments and strings are masked before either scan. This does not interpret
    declarations, #check commands, or unrelated arrays of quoted Names as imports.
    """
    clean = code_only(source)
    result = set()
    for m in re.finditer(r'(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]*)', clean):
        for word in m[1].split():
            if not re.fullmatch(NAME, word):
                raise ValueError('unsupported audit import: ' + word)
            result.add(word)
    for call in re.finditer(r'\b(?:Lean\.)?importModules\b', clean):
        pos = call.end()
        while pos < len(clean) and (clean[pos].isspace() or clean[pos] == '('): pos += 1
        if not clean.startswith('#[', pos):
            raise ValueError('importModules requires a literal array (line %d)' % (clean.count('\n', 0, pos)+1))
        end = _array_end(clean, pos+1)
        body = clean[pos+2:end]
        # Split record entries only at the top level; nested field values may contain commas.
        entries, begin, stack = [], 0, []
        for i, char in enumerate(body):
            if char in '{[(': stack.append(char)
            elif char in '}])':
                if not stack or {'}': '{', ']': '[', ')': '('}[char] != stack.pop():
                    raise ValueError('unbalanced importModules record')
            elif char == ',' and not stack:
                entries.append(body[begin:i]); begin = i+1
        if stack: raise ValueError('unbalanced importModules record')
        entries.append(body[begin:])
        for entry in entries:
            if not entry.strip(): continue
            if not (entry.strip().startswith('{') and entry.strip().endswith('}')):
                raise ValueError('importModules entries must be literal Import records')
            assignments = list(re.finditer(r'\bmodule\s*:=', entry))
            names = re.findall(r'\bmodule\s*:=\s*`('+NAME+r')\s*(?=[,}])', entry)
            if len(assignments) != 1 or len(names) != 1:
                raise ValueError('importModules module must be one literal Name')
            result.add(names[0])
    return result


def audit_build_targets(sources):
    return sorted({n for source in sources for n in audit_imports(source)
                   if n == 'SerrePositivity' or n.startswith('SerrePositivity.')})
