"""Combine reviewed environment owners and preserve private kernel identities."""
import re
from pathlib import Path

from layer_check import code_only

GENERATED = re.compile(r'(?:_?match_\d+|eq_\d+|_?proof_\d+(?:_\d+)*|_sunfold|_unsafe_rec|_cstage\d*)')
PRIVATE_DECL = re.compile(r'\bprivate\s+(?:(?:noncomputable|unsafe|partial)\s+)*(?:def|theorem|lemma|abbrev|opaque|axiom|structure|class|inductive|instance)\s+([\w.\']+)')


def private_collisions(resolutions, root):
    """An explicitly written declaration wins over a generated-looking spelling."""
    groups = {}
    for name, aliases in resolutions.items():
        if isinstance(aliases, str):
            continue
        if not aliases or not all(a['raw'].startswith('_private.') and a['module'] for a in aliases):
            raise ValueError('expected private kernel constants for ' + name)
        generated = any(GENERATED.fullmatch(part) for part in name.split('.'))
        for alias in aliases:
            path = Path(root) / (alias['module'].replace('.', '/') + '.lean')
            if not path.exists():
                path = Path(root) / '.lake/packages/mathlib' / (alias['module'].replace('.', '/') + '.lean')
            if not path.exists():
                raise ValueError('missing source for private owner: ' + alias['module'])
            if any(name == n or name.endswith('.' + n) for n in PRIVATE_DECL.findall(code_only(path.read_text()))):
                generated = False
        groups[name] = {'generated': generated, 'aliases': sorted(aliases, key=lambda a: (a['module'], a['raw']))}
    return groups


def combine_rows(entries, owners, private=None):
    rows = {}
    skipped = set()
    used = set()
    private = private or {}
    for record, transient in entries:
        name = record['name']
        if name in owners:
            record = {**record, 'module': owners[name]}
            transient = True
            used.add(name)
        elif name in private:
            group = private[name]
            if not any(alias['module'] == record['module'] for alias in group['aliases']):
                raise ValueError('unverified private owner: ' + str((name, record['module'])))
            transient = group['generated']
            used.add(name)
        key = name, record['module']
        if key in rows and rows[key] != record:
            raise ValueError(f'different records for {key!r}')
        rows[key] = record
        if transient:
            skipped.add(key)
    if unused := (owners.keys() | private.keys()) - used:
        raise ValueError('unused environment owners: ' + repr(sorted(unused)))
    return rows, skipped
