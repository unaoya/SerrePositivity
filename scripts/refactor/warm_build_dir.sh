#!/bin/zsh
# 概要：別 worktree の build だけを複製し、未ビルドの起点を表示する。
# 方針：manifest 同一・複製元の lake build 不在を確認して一回だけ rsync。
# 規約：--yes は実行中ビルドの終了を待つ指定。packages は触らない。
# 使われ方：zsh scripts/refactor/warm_build_dir.sh --from ../SerrePositivity [--yes]
exec python3 - "$@" <<'PY'
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

p=argparse.ArgumentParser(description='Copy .lake/build once; never build or copy packages.')
p.add_argument('--from',dest='source',type=Path,default=Path('../SerrePositivity'))
p.add_argument('--yes',action='store_true',help='wait if the source has a running lake build')
a=p.parse_args()
root=Path.cwd().resolve(); source=a.source.resolve()

def source_builds():
    ps=subprocess.run(['ps','-axo','pid=,comm=,args='],capture_output=True,text=True)
    if ps.returncode: raise RuntimeError('cannot inspect processes: '+ps.stderr.strip())
    active=[]
    for line in ps.stdout.splitlines():
        fields=line.strip().split(None,2)
        if len(fields)!=3 or Path(fields[1]).name!='lake' or not re.search(r'(?:^|\s)(?:\S*/)?lake\s+build(?:\s|$)',fields[2]): continue
        result=subprocess.run(['lsof','-a','-p',fields[0],'-d','cwd','-Fn'],capture_output=True,text=True)
        if result.returncode:
            # A process may finish between ps and lsof. A live unreadable cwd is unsafe.
            try: os.kill(int(fields[0]),0)
            except ProcessLookupError: continue
            raise RuntimeError('cannot inspect live lake cwd: '+fields[0])
        cwd=[l[1:] for l in result.stdout.splitlines() if l.startswith('n')]
        if not cwd: raise RuntimeError('lsof returned no cwd for lake '+fields[0])
        if any(Path(c).resolve()==source for c in cwd): active.append(fields[0])
    return active

def vanished_outputs(log):
    """Accept only fully explained vanish failures, never generic rc=23 failures."""
    paths=[]; unexpected=[]
    for line in log.splitlines():
        if not line.strip(): continue
        match=re.search(r'^file has vanished: ["\'](.+?)["\']\s*$',line)
        if match is None:
            match=re.search(r'^rsync(?:\([^)]*\))?: (?:\[sender\] )?(?:link_stat|readlink_stat|open|stat):? ["\'](.+?)["\'](?: failed)?:? No such file or directory(?: \(2\))?\s*$',line)
        darwin=re.search(r'^rsync\(\d+\): error: (.+): (?:open|stat|lstat) \(2\) in (.+): No such file or directory$',line)
        if match or darwin:
            raw=Path((match or darwin)[1])
            path=raw if raw.is_absolute() else ((Path(darwin[2])/raw) if darwin else source/'.lake/build'/raw)
            # Resolve the parent as well to reject packages, traversal and symlink escapes.
            try: rel=path.resolve().relative_to((source/'.lake/build/lib/lean').resolve())
            except ValueError: unexpected.append(line);continue
            if not re.search(r'\.(?:olean(?:\.(?:private|server))?|ilean|ir(?:\.sig)?|c|trace|hash)(?:\.hash)?$',str(rel)):
                unexpected.append(line);continue
            paths.append(str(path))
        elif re.fullmatch(r'rsync (?:error|warning): (?:some files/attrs were not transferred.*\(code 23\).*|some files vanished before they could be transferred.*\(code 24\).*)',line):
            continue
        elif re.fullmatch(r'rsync(?:\([^)]*\))?: (?:\[sender\] )?warning: (?:child|receiver) .*exited with status (?:23|24)',line):
            continue
        else: unexpected.append(line)
    return sorted(set(paths)),unexpected

try:
    if root==source: raise RuntimeError('source and destination must differ')
    if (root/'lake-manifest.json').read_bytes()!=(source/'lake-manifest.json').read_bytes():
        raise RuntimeError('lake-manifest.json differs; packages are not copied')
    src=source/'.lake/build'; dst=root/'.lake/build'
    if not src.is_dir(): raise RuntimeError('source build directory missing')
    if src.resolve().is_relative_to(dst.resolve()) or dst.resolve().is_relative_to(src.resolve()): raise RuntimeError('build directories alias or contain each other')
    active=source_builds()
    if active and not a.yes: raise RuntimeError('source lake build is running: '+','.join(active)+'; use --yes to wait')
    last=0
    while active:
        if time.monotonic()-last>=60:
            print('waiting for source lake build: '+','.join(active),flush=True);last=time.monotonic()
        time.sleep(10);active=source_builds()
    # Recheck manifests after waiting.
    if (root/'lake-manifest.json').read_bytes()!=(source/'lake-manifest.json').read_bytes(): raise RuntimeError('manifest changed while waiting')
    dst.mkdir(parents=True,exist_ok=True)
    result=subprocess.run(['rsync','-a','--delete',str(src)+'/',str(dst)+'/'],capture_output=True,text=True)
    log=result.stdout+result.stderr
    fd,logpath=tempfile.mkstemp(prefix='serre-warm-build-',suffix='.log')
    with os.fdopen(fd,'w') as f: f.write(log)
    print('rsync log: '+logpath,flush=True)
    if result.returncode:
        vanished,other=vanished_outputs(log)
        if result.returncode not in (23,24) or not 0<len(vanished)<50 or other:
            print(log,file=sys.stderr);raise RuntimeError(f'rsync failed ({result.returncode}); unaccepted errors, paths, or count')
        print(f'accepted rsync {result.returncode}: {len(vanished)} vanished outputs\n'+'\n'.join(vanished),flush=True)
    probe=subprocess.run(['lake','build','SerrePositivity','--no-build'],capture_output=True,text=True)
    output=probe.stdout+probe.stderr
    print('\n'.join(output.splitlines()[:20]))
    missing=[l for l in output.splitlines() if re.search(r'(?i)(needs? (?:to be )?(?:built|rebuilt)|not (?:yet )?built|build (?:is )?required|--no-build|has not been built)',l)]
    if probe.returncode and not missing: raise RuntimeError(f'no-build probe failed unexpectedly ({probe.returncode})')
    print(f'未ビルドの起点: {len(missing)}（診断行数、no-build 終了コード {probe.returncode}）')
except (OSError,RuntimeError) as exc:
    print('warm_build_dir: '+str(exc),file=sys.stderr);sys.exit(1)
PY
