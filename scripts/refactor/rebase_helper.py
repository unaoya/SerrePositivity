#!/usr/bin/env python3
"""Rewrite only imports in untracked/uncommitted Lean files of an explicitly selected worktree."""
import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess

from layer_check import code_only, imports
from lean_source import add_import, uses_names, read_source, write_source


def dirty_lean_files(root):
    top=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip()).resolve()
    if top!=root.resolve():raise ValueError('--worktree must be the Git checkout root')
    fields=subprocess.check_output(['git','status','--porcelain=v1','-z','--untracked-files=all'],cwd=root).decode().split('\0')
    paths=[];i=0
    while i<len(fields) and fields[i]:
        row=fields[i];i+=1
        if 'R' in row[:2] or 'C' in row[:2]:i+=1
        path=root/row[3:]
        if path.suffix=='.lean' and path.is_file():
            if not path.resolve().is_relative_to(root.resolve()) or path.is_symlink():raise ValueError('file escapes worktree')
            paths.append(path)
    return sorted(set(paths))


def rewrite(text,moves,declarations):
    mask=code_only(text)
    pattern=re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)')
    matches=list(pattern.finditer(mask))
    if {m[1] for m in matches}!=imports(text):raise ValueError('unsupported import layout; review manually')
    for m in reversed(matches):
        if m[1] in moves:text=text[:m.start(1)]+moves[m[1]]+text[m.end(1):]
    for module in sorted({m for n,m in declarations.items() if uses_names(text,[n])}):
        text=add_import(text,module)
    return text


def mapping(path,key):
    data=json.loads(path.read_text());value=data.get(key,{})
    if not isinstance(value,dict) or not all(isinstance(k,str) and isinstance(v,str) and re.fullmatch(r"[\w']+(?:\.[\w']+)*",v) for k,v in value.items()):
        raise ValueError('invalid mapping: '+key)
    return value


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worktree',type=Path,required=True)
    p.add_argument('--moves',type=Path);p.add_argument('--split',type=Path,action='append',default=[])
    mode=p.add_mutually_exclusive_group();mode.add_argument('--apply',action='store_true');mode.add_argument('--dry-run',action='store_true')
    args=p.parse_args()
    try:
        if not args.moves and not args.split:raise ValueError('provide --moves and/or --split')
        moves=mapping(args.moves,'moves') if args.moves else {};declarations={}
        for path in args.split:
            for n,m in mapping(path,'declaration_modules').items():
                if n in declarations and declarations[n]!=m:raise ValueError('conflicting declaration map: '+n)
                declarations[n]=m
        changes=[]
        for path in dirty_lean_files(args.worktree):
            before=read_source(path);after=rewrite(before,moves,declarations)
            if before!=after:changes.append((path,before,after))
        for path,before,after in changes:
            print(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=str(path),tofile=str(path))),end='')
        if args.apply:
            for path,before,_ in changes:
                if read_source(path)!=before:raise ValueError('file changed during planning: '+str(path))
            for path,_,after in changes:write_source(path,after)
        print(('APPLIED' if args.apply else 'DRY RUN')+f': {len(changes)} files')
        return 0
    except (OSError,ValueError,subprocess.CalledProcessError) as exc:
        print('rebase_helper: STOP: '+str(exc));return 1


if __name__=='__main__':raise SystemExit(main())
