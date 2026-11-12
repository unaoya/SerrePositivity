#!/usr/bin/env python3
"""Memory-budgeted audit scheduling, RSS measurements, and serial environment retries."""
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import time

from layer_check import read_graph
from audit_imports import audit_imports

ROOT=Path(__file__).resolve().parents[2]


def cache_key(root, path, graph, memo=None):
    memo={} if memo is None else memo
    source=(root/path).read_bytes()
    pending=list(audit_imports(source.decode()));seen=set()
    while pending:
        mod=pending.pop()
        if mod in seen or mod not in graph:continue
        seen.add(mod);pending.extend(graph[mod])
    h=hashlib.sha256()
    def add(name,data):
        h.update(name.encode()+b'\0'+str(len(data)).encode()+b'\0'+data)
    add('schema',b'IF-F-cache-v2')
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


import datetime
import math
import queue
import threading

GB = 1_000_000_000
UNKNOWN_RSS_BYTES = 20 * GB


def memory_budget(value):
    number = float(value)
    if not math.isfinite(number) or number < 0:
        raise ValueError('VERIFY_MEMORY_GB must be finite and nonnegative')
    return int(number * GB)


def read_stats(root):
    try:
        data = json.loads((root/'.lake/verify/audit-stats.json').read_text())
        return {name: row for name, row in data.items()
                if isinstance(row, dict) and isinstance(row.get('max_rss_bytes'), int)
                and row['max_rss_bytes'] >= 0
                and isinstance(row.get('seconds'), (int, float))
                and math.isfinite(row['seconds']) and row['seconds'] >= 0}
    except (OSError, ValueError, TypeError, AttributeError):
        return {}


def save_stat(root, record, stats, commit):
    if record.get('cached') or record.get('max_rss_bytes') is None:
        return
    stats[record['name']] = {key: record[key] for key in ('seconds', 'max_rss_bytes', 'measured_at')}
    stats[record['name']]['commit'] = commit
    target = root/'.lake/verify/audit-stats.json'
    temporary = target.with_suffix('.tmp')
    temporary.write_text(json.dumps(stats, ensure_ascii=False, indent=2)+'\n')
    temporary.replace(target)


def parse_time_output(text):
    match = re.search(r'(?m)^\s*(\d+)\s+maximum resident set size\s*$', text)
    return int(match[1]) if match else None  # macOS reports bytes, not KiB.


def timed_tree_rss(text, parent_pid):
    """RSS of this runner's /usr/bin/time children and their descendants, in bytes."""
    rows = {}
    for line in text.splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) != 4:
            continue
        try:
            pid, parent, rss = map(int, fields[:3])
        except ValueError:
            continue
        rows[pid] = (parent, rss * 1024, fields[3])  # ps reports KiB.
    selected = {pid for pid, (parent, _, command) in rows.items()
                if parent == parent_pid and Path(command).name == 'time'}
    while True:
        expanded = selected | {pid for pid, (parent, _, _) in rows.items() if parent in selected}
        if expanded == selected:
            return sum(rows[pid][1] for pid in selected)
        selected = expanded


class RSSSampler:
    """Sample simultaneous process-tree RSS; individual peaks come from time -l."""
    def __init__(self, interval=0.5):
        self.interval = interval
        self.stopped = threading.Event()
        self.report = {'interval_seconds': interval, 'max_simultaneous_rss_bytes': 0,
                       'samples': 0, 'errors': []}
        self.thread = threading.Thread(target=self.sample, daemon=True)

    def sample(self):
        while not self.stopped.is_set():
            try:
                result = subprocess.run(['ps', '-axo', 'pid=,ppid=,rss=,comm='],
                                        capture_output=True, text=True, timeout=5)
                if result.returncode:
                    raise RuntimeError(result.stderr.strip())
                rss = timed_tree_rss(result.stdout, os.getpid())
                self.report['max_simultaneous_rss_bytes'] = max(
                    self.report['max_simultaneous_rss_bytes'], rss)
                self.report['samples'] += 1
            except (OSError, RuntimeError, subprocess.TimeoutExpired) as exc:
                message = str(exc)
                if message not in self.report['errors']:
                    self.report['errors'].append(message)
            self.stopped.wait(self.interval)

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *args):
        self.stopped.set()
        self.thread.join()


def schedule_checks(paths, action, stats, jobs, budget_bytes, on_complete=lambda r: None,
                    exclusive_paths=()):
    """Unknown first, then longest first; dispatch the first task that fits."""
    if jobs < 1 or budget_bytes < 0:
        raise ValueError('invalid scheduler limits')
    exclusive = set(exclusive_paths)
    if not exclusive <= set(paths):
        raise ValueError('exclusive audits must be scheduled audit paths')
    pending = sorted(paths, key=lambda p: (p in stats, -stats.get(p, {}).get('seconds', 0), p))
    estimate = {p: stats.get(p, {}).get('max_rss_bytes', UNKNOWN_RSS_BYTES) for p in pending}
    report = {'planned_order': pending[:], 'start_order': [], 'events': [],
              'memory_budget_bytes': budget_bytes, 'unknown_rss_bytes': UNKNOWN_RSS_BYTES,
              'max_concurrent': 0, 'max_reserved_rss_bytes': 0,
              'exclusive_audits': sorted(exclusive), 'max_exclusive_concurrent': 0,
              'memory_wait_count': 0, 'memory_wait_seconds': 0.0}
    active, results, threads = {}, [], []
    ready = queue.Queue()
    started = time.monotonic()
    def fits(path):
        if path in exclusive and exclusive.intersection(active):
            return False
        return not budget_bytes or sum(active.values()) + estimate[path] <= budget_bytes
    def event(kind, **fields):
        report['events'].append({'event': kind, 'at_seconds': round(time.monotonic()-started, 6), **fields})
    def worker(path):
        try:
            ready.put((path, action(path), None))
        except BaseException as exc:
            ready.put((path, None, exc))
    try:
        while pending or active:
            while pending and len(active) < jobs:
                fit = next((p for p in pending if fits(p)), None)
                # A single audit larger than the budget must not deadlock the queue.
                oversize = fit is None and not active
                if oversize:
                    fit = pending[0]
                if fit is None:
                    break
                pending.remove(fit); active[fit] = estimate[fit]
                report['start_order'].append(fit)
                report['max_concurrent'] = max(report['max_concurrent'], len(active))
                report['max_exclusive_concurrent'] = max(
                    report['max_exclusive_concurrent'], len(exclusive.intersection(active)))
                report['max_reserved_rss_bytes'] = max(report['max_reserved_rss_bytes'], sum(active.values()))
                event('start', name=fit, estimated_rss_bytes=estimate[fit],
                      reserved_rss_bytes=sum(active.values()), concurrent=len(active), oversize_alone=oversize,
                      exclusive=fit in exclusive)
                thread = threading.Thread(target=worker, args=(fit,)); threads.append(thread); thread.start()
            blocked = bool(pending and len(active) < jobs
                           and not any(fits(p) for p in pending))
            if blocked:
                report['memory_wait_count'] += 1
                event('memory_wait', reserved_rss_bytes=sum(active.values()), pending=pending[:], active=list(active))
            wait_started = time.monotonic()
            path, result, error = ready.get()
            if blocked:
                report['memory_wait_seconds'] += time.monotonic() - wait_started
            active.pop(path)
            event('finish', name=path, concurrent=len(active))
            if error:
                raise error
            results.append(result); on_complete(result)
    finally:
        for thread in threads:
            thread.join()
    report['memory_wait_seconds'] = round(report['memory_wait_seconds'], 3)
    return results, report


def execute(root,kind,path,key,use_cache,attempt=1):
    started=time.monotonic()
    out=root/'.lake/verify'
    suffix='' if attempt==1 else '-retry-'+str(attempt-1)
    stem=kind+'-'+hashlib.sha256(path.encode()).hexdigest()[:20]+suffix
    log=out/(stem+'.log'); timing=out/(stem+'.time')
    cache=out/'cache'/(str(key)+'.json')
    cached=read_cache(cache,key) if use_cache and key else None
    rss=None; measured_at=None
    if cached is not None:
        log.write_text(cached);rc=0
        rss=read_stats(root).get(path,{}).get('max_rss_bytes')
    else:
        timing.unlink(missing_ok=True)
        with log.open('w') as handle:
            try:
                rc=subprocess.call(['/usr/bin/time','-l','-o',str(timing.resolve()),
                                    'lake','env','lean',path],cwd=root,stdout=handle,stderr=subprocess.STDOUT)
            except OSError as exc:handle.write(str(exc)+'\n');rc=1
        measured_at=datetime.datetime.now(datetime.timezone.utc).isoformat()
        if timing.exists():rss=parse_time_output(timing.read_text(errors='replace'))
        if rc==0 and key:
            output=log.read_text(errors='replace')
            value={'key':key,'exit_code':0,'output':output,'output_sha256':hashlib.sha256(output.encode()).hexdigest()}
            temp=cache.with_suffix('.tmp');temp.write_text(json.dumps(value,ensure_ascii=False)+'\n');temp.replace(cache)
    return {'kind':kind,'name':path,'exit_code':rc,'seconds':round(time.monotonic()-started,3),
            'log':str(log.relative_to(root)),'cached':cached is not None,'cache_key':key,
            'max_rss_bytes':rss,'measured_at':measured_at,'time_log':str(timing.relative_to(root)) if cached is None else None}



HEAVY_AUDIT = 'scripts/audit_axioms.lean'
SORRY = 'scripts/refactor/audit_sorries.lean'


def environment_failure(root, record):
    """Only retry environment diagnostics; a genuinely missing object is not transient.

    Inspect after the pool has joined. Mixed semantic/environment errors stay failures.
    """
    if record['exit_code'] == 0:
        return []
    text = re.sub(r'\x1b\[[0-9;]*[A-Za-z]', '', (root / record['log']).read_text(errors='replace'))
    messages = re.findall(r'(?m)^(?:.*?:\d+:\d+: )?(?:fatal )?error(?:\([^)]*\))?:\s*(.*)$', text)
    if not messages:
        # subprocess startup OSError has no Lean diagnostic prefix.
        messages = [line.strip() for line in text.splitlines() if line.strip()]
    reasons = []
    for message in messages:
        if 'Too many open files' in message:
            reasons.append('too-many-open-files')
        elif message.startswith('failed to open file'):
            reasons.append('failed-to-open-file')
        elif match := re.fullmatch(r"object file '([^']+)' of module \S+ does not exist", message):
            path = Path(match[1])
            if not (path if path.is_absolute() else root / path).is_file():
                return []
            reasons.append('object-file-exists-after-failure')
        else:
            return []
    return sorted(set(reasons))


def retry_environment_failure(root, record):
    """At most one uncached retry. Preserve the first log and both exit codes."""
    reasons = environment_failure(root, record)
    attempts = [dict(record)]
    if reasons:
        attempts.append(execute(root, record['kind'], record['name'], record['cache_key'],
                                False, attempt=2))
    final = dict(attempts[-1])
    final.update(retried=bool(reasons), retry_reason=reasons, attempts=attempts,
                 seconds=round(sum(r['seconds'] for r in attempts), 3))
    peaks = [r.get('max_rss_bytes') for r in attempts if r.get('max_rss_bytes') is not None]
    if peaks: final['max_rss_bytes'] = max(peaks)
    return final


def run_checks(root, audits, keys, jobs, use_cache, memory_gb=40, telemetry=None):
    """Join scheduled audits before serial retries, audit_axioms, and sorry.

    VERIFY_EXCLUSIVE_AUDITS names a whitespace-separated mutual exclusion group;
    it constrains concurrency without changing the selected audits or their checks.
    """
    out = root / '.lake/verify'
    stats = read_stats(root)
    git = subprocess.run(['git','rev-parse','HEAD'], cwd=root, capture_output=True, text=True)
    commit = git.stdout.strip() if git.returncode == 0 else 'unknown'
    completed = 0
    def progress():
        (out/'audit-progress.json').write_text(json.dumps({'completed':completed,'total':len(audits)})+'\n')
        print(f'audit progress: {completed}/{len(audits)}', flush=True)
    def record(result):
        save_stat(root, result, stats, commit)
    def completed_audit(result):
        nonlocal completed
        record(result); completed += 1; progress()
    progress()
    started = time.monotonic()
    normal = [p for p in audits if p != HEAVY_AUDIT]
    exclusive = set(os.environ.get('VERIFY_EXCLUSIVE_AUDITS', '').split())
    if not exclusive <= set(audits):
        raise ValueError('VERIFY_EXCLUSIVE_AUDITS contains an unselected audit')
    initial, scheduling = schedule_checks(normal,
        lambda p: execute(root, 'audit', p, keys[p], use_cache),
        dict(stats), jobs, memory_budget(memory_gb), completed_audit,
        exclusive_paths=exclusive.intersection(normal))
    pool_seconds = round(time.monotonic()-started, 3)
    records = []
    for first in initial:
        final = retry_environment_failure(root, first)
        if final['retried']:record(final)
        records.append(final)
    if HEAVY_AUDIT in audits:
        heavy = retry_environment_failure(root,
            execute(root, 'audit', HEAVY_AUDIT, keys[HEAVY_AUDIT], use_cache))
        records.append(heavy); completed_audit(heavy)
    audit_seconds = round(time.monotonic()-started, 3)
    records.sort(key=lambda r:r['name'])
    sorry = retry_environment_failure(root, execute(root, 'sorry', SORRY, keys[SORRY], use_cache))
    records.append(sorry); record(sorry)
    if telemetry is not None:telemetry.update(scheduling)
    return records, pool_seconds, audit_seconds


def main():
    out=ROOT/'.lake/verify';(out/'cache').mkdir(exist_ok=True)
    audits=sorted((out/'audits.txt').read_text().splitlines())
    (out/'audit-progress.json').write_text(json.dumps({'completed':0,'total':len(audits)})+'\n')
    jobs=int(os.environ.get('VERIFY_JOBS','6'));use_cache=os.environ.get('VERIFY_CACHE','0')=='1'
    config=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
    graph,_=read_graph(ROOT,config)
    memo={};keys={};errors={}
    for p in [*audits,SORRY]:
        try:
            if any(k in os.environ for k in ('SORRY_AUDIT_ROOT','SORRY_AUDIT_ALLOWED')):
                keys[p]=None
            else:keys[p]=cache_key(ROOT,p,graph,memo)
        except (OSError,ValueError) as exc:
            keys[p]=None;errors[p]=str(exc)
    scheduling={}
    with RSSSampler() as sampler:
        records,pool_seconds,audit_seconds=run_checks(ROOT,audits,keys,jobs,use_cache,
            os.environ.get('VERIFY_MEMORY_GB','40'),scheduling)
    with (out/'stages.tsv').open('a') as stages, (ROOT/'scripts/refactor/verify.log').open('a') as combined:
        for r in records:
            stages.write(f"{r['kind']}\t{r['name']}\t{r['exit_code']}\t{r['seconds']:.3f}\t{r['log']}\n")
            line=f"{r['kind']} {r['name']} rc={r['exit_code']} {r['seconds']}s cached={r['cached']} retried={r['retried']}"
            print(line,flush=True);combined.write(line+'\n')
            for i,attempt in enumerate(r['attempts'],1):
                combined.write(f"attempt {i} rc={attempt['exit_code']} log={attempt['log']}\n")
                combined.write((ROOT/attempt['log']).read_text(errors='replace')+'\n')
    (out/'runner.json').write_text(json.dumps({'jobs':jobs,'cache_enabled':use_cache,
        'audit_pool_wall_seconds':pool_seconds,'audit_wall_seconds':audit_seconds,
        'retried':sum(r['retried'] for r in records),
        'cache_unavailable':errors,'scheduling':scheduling,'rss_sampling':sampler.report,
        'measurement_missing':[r['name'] for r in records if not r['cached'] and r['max_rss_bytes'] is None],
        'stages':records},ensure_ascii=False,indent=2)+'\n')
    return 0


if __name__=='__main__':raise SystemExit(main())
