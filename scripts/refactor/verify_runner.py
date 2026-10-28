#!/usr/bin/env python3
"""Parallel audits and success-only dependency-hash cache for verify.sh."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from layer_check import imports, read_graph

ROOT=Path(__file__).resolve().parents[2]


def cache_key(root, path, graph, memo=None):
    memo={} if memo is None else memo
    source=(root/path).read_bytes()
    pending=list(imports(source.decode()));seen=set()
    while pending:
        mod=pending.pop()
        if mod in seen or mod not in graph:continue
        seen.add(mod);pending.extend(graph[mod])
    h=hashlib.sha256()
    def add(name,data):
        h.update(name.encode()+b'\0'+str(len(data)).encode()+b'\0'+data)
    add('schema',b'IF-W0-2-cache-v1')
    add('path',path.encode());add('source',source)
    for name in ['lean-toolchain','lake-manifest.json']:
        add(name,(root/name).read_bytes())
    # Helper changes are as significant as changes to verify.sh itself.
    for p in sorted((root/'scripts/refactor').glob('*')):
        if p.suffix in ('.sh','.py','.lean'):
            add(str(p.relative_to(root)),p.read_bytes())
    for mod in sorted(seen):
        p=root/'.lake/build/lib/lean'/(mod.replace('.','/')+'.olean.hash')
        if mod not in memo:memo[mod]=p.read_bytes()
        add(mod,memo[mod])
    return h.hexdigest()


def read_cache(path,key):
    try:
        value=json.loads(path.read_text())
        if value['key']!=key or value['exit_code']!=0:return None
        log=value['output']
        if hashlib.sha256(log.encode()).hexdigest()!=value['output_sha256']:return None
        return log
    except (OSError,ValueError,KeyError,TypeError):return None


def execute(root,kind,path,key,use_cache):
    started=time.monotonic()
    out=root/'.lake/verify'
    log=out/(kind+'-'+hashlib.sha256(path.encode()).hexdigest()[:20]+'.log')
    cache=out/'cache'/(str(key)+'.json')
    cached=read_cache(cache,key) if use_cache and key else None
    if cached is not None:
        log.write_text(cached);rc=0
    else:
        with log.open('w') as handle:
            try:rc=subprocess.call(['lake','env','lean',path],cwd=root,stdout=handle,stderr=subprocess.STDOUT)
            except OSError as exc:handle.write(str(exc)+'\n');rc=1
        if rc==0 and key:
            output=log.read_text(errors='replace')
            value={'key':key,'exit_code':0,'output':output,'output_sha256':hashlib.sha256(output.encode()).hexdigest()}
            temp=cache.with_suffix('.tmp');temp.write_text(json.dumps(value,ensure_ascii=False)+'\n');temp.replace(cache)
    return {'kind':kind,'name':path,'exit_code':rc,'seconds':round(time.monotonic()-started,3),
            'log':str(log.relative_to(root)),'cached':cached is not None,'cache_key':key}


def main():
    out=ROOT/'.lake/verify';(out/'cache').mkdir(exist_ok=True)
    audits=sorted((out/'audits.txt').read_text().splitlines())
    (out/'audit-progress.json').write_text(json.dumps({'completed':0,'total':len(audits)})+'\n')
    jobs=int(os.environ.get('VERIFY_JOBS','3'));use_cache=os.environ.get('VERIFY_CACHE','0')=='1'
    config=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
    graph,_=read_graph(ROOT,config)
    memo={};keys={};errors={}
    sorry='scripts/refactor/audit_sorries.lean'
    for p in [*audits,sorry]:
        try:
            if any(k in os.environ for k in ('SORRY_AUDIT_ROOT','SORRY_AUDIT_ALLOWED')):
                keys[p]=None
            else:keys[p]=cache_key(ROOT,p,graph,memo)
        except (OSError,ValueError) as exc:
            keys[p]=None;errors[p]=str(exc)
    started=time.monotonic()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures=[pool.submit(execute,ROOT,'audit',p,keys[p],use_cache) for p in audits]
        for completed,future in enumerate(as_completed(futures),1):
            future.result()
            (out/'audit-progress.json').write_text(json.dumps({'completed':completed,'total':len(audits)})+'\n')
            print(f'audit progress: {completed}/{len(audits)}',flush=True)
        records=[f.result() for f in futures]
    audit_seconds=round(time.monotonic()-started,3)
    records.append(execute(ROOT,'sorry',sorry,keys[sorry],use_cache))
    with (out/'stages.tsv').open('a') as stages, (ROOT/'scripts/refactor/verify.log').open('a') as combined:
        for r in records:
            stages.write(f"{r['kind']}\t{r['name']}\t{r['exit_code']}\t{r['seconds']:.3f}\t{r['log']}\n")
            line=f"{r['kind']} {r['name']} rc={r['exit_code']} {r['seconds']}s cached={r['cached']}"
            print(line,flush=True);combined.write(line+'\n'+(ROOT/r['log']).read_text(errors='replace')+'\n')
    (out/'runner.json').write_text(json.dumps({'jobs':jobs,'cache_enabled':use_cache,
        'audit_wall_seconds':audit_seconds,'cache_unavailable':errors,'stages':records},ensure_ascii=False,indent=2)+'\n')
    return 0


if __name__=='__main__':raise SystemExit(main())
