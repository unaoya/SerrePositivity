#!/usr/bin/env python3
"""調整役の取り込みの検証（2026-11-17〜19 に使ったものを main に置く）。
使い方（main の root で、未コミットの merge を作った後）：
  nohup python3 scripts/coord/merge_check.py <出力ディレクトリ> "<ラベル>" > <出力ディレクトリ>/merge.out 2>&1 &
鍵 coord を短い塊で取り直しながら、root → 監査の対象 → 監査の束（並列 6）→ sorry の閉包。失敗したら STOP を書いて止まる。
最後の行が MERGE-CHECKS-DONE なら全部通った。前回の束の結果（<出力ディレクトリ>/*-batch-*.json）があれば、所要時間の見積もりに使う。
検証中は $TMPDIR/serre-lake-build.day-capacity を 1 に、終わったら 2 に戻す（手で）。"""
import json, os, re, subprocess, sys, time, pathlib
MAIN = pathlib.Path(__file__).resolve().parents[2]; MERGE = MAIN
S = pathlib.Path(sys.argv[1]).resolve(); S.mkdir(parents=True, exist_ok=True)
LABEL = sys.argv[2] if len(sys.argv) > 2 else 'merge'
LOG = S/'merge.log'; RES = S/'merge_results.json'
res = {'stages': []}
def log(*a):
    line = time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a)
    print(line, flush=True); open(LOG, 'a').write(line + '\n')
def save(): RES.write_text(json.dumps(res, ensure_ascii=False, indent=1))
def yield_to_lanes():
    """coord は常に先頭なので、待っているレーンの整理券があれば、それが鍵を取って放すまで待つ（最大 35 分）。"""
    t0 = time.time()
    while time.time() - t0 < 2100:
        st = subprocess.run(['zsh', 'scripts/refactor/with_build_lock.sh', '--status'], cwd=MAIN, capture_output=True, text=True).stdout
        m = re.search(r'queue \(day order\): (\d+)', st)
        waiting = int(m.group(1)) if m else 0
        busy = 'holder: (free)' not in st and 'SerrePositivity-merge' not in st
        if waiting == 0: return   # 待っている整理券がなければ進む（枠が使われているだけなら待たない）
        time.sleep(30)
def locked(cwd, cmd, timeout):
    yield_to_lanes()
    full = ['zsh', 'scripts/refactor/with_build_lock.sh', '--class', 'coord', '--wait', '7200', '--',
            'gtimeout', '--kill-after=10s', f'{timeout}s'] + cmd
    t = time.time(); p = subprocess.run(full, cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr, time.time() - t
def chunked_build(cwd, targets, name, chunk=600):
    n = 0
    while True:
        n += 1
        rc, out, dt = locked(cwd, ['lake', 'build'] + targets, chunk)
        errs = [l for l in out.splitlines() if l.startswith('error') or ': error:' in l]
        log(f'{name} chunk {n}: rc={rc} {dt:.0f}s', 'errors=' + str(len(errs)))
        if 'Build completed successfully' in out and rc == 0:
            res['stages'].append({'stage': name, 'chunks': n, 'ok': True}); save(); return True
        if errs and rc not in (124, 137):
            (S/f'{name}-errors.log').write_text(out[-20000:])
            res['stages'].append({'stage': name, 'chunks': n, 'ok': False}); save(); return False
        if rc not in (0, 124, 137):
            (S/f'{name}-errors.log').write_text(out[-20000:])
            res['stages'].append({'stage': name, 'chunks': n, 'ok': False, 'rc': rc}); save(); return False
def timed_lean(cwd, path, timeout):
    rc, out, dt = locked(cwd, ['/usr/bin/time', '-l', 'lake', 'env', 'lean', str(path)], timeout)
    m = re.search(r'(\d+)\s+maximum resident set size', out)
    return rc, (int(m.group(1)) if m else None), dt, out
# 1. A1 の計測は監査の束（4.）の中で「後」の版を測る。「前」は ③-b の 11-17 の実測（audit-stats.json）
head = f'uncommitted merge ({LABEL}) into '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=MAIN,text=True).strip(); res['head']=head; save(); log(head)
if not chunked_build(MERGE, ['SerrePositivity'], 'root'): log('STOP: root failed'); sys.exit(1)
# 3. 監査の対象（監査スクリプトの import）
audits = [l.strip() for l in open(MERGE/'scripts/refactor/audit_manifest.txt') if l.strip() and not l.startswith('#')]
targets = sorted({m for a in audits if (MERGE/a).exists() for m in re.findall(r'^import\s+(SerrePositivity\.[A-Za-z0-9_.]+)', (MERGE/a).read_text(), re.M)})
log(f'{len(audits)} audits, {len(targets)} audit build targets')
for i in range(0, len(targets), 400):
    if not chunked_build(MERGE, targets[i:i+400], f'audit-targets-{i//400}'): log('STOP: audit targets failed'); sys.exit(1)
# 4. 監査を束で（一束 12 分・並列 6・メモリ 40 GB を目安）
stats = {}
for f in sorted(S.glob('*-batch-*.json')):
    for r in json.loads(f.read_text()):
        stats[r['audit']] = {'seconds': r['seconds'], 'max_rss_bytes': int((r['rss_gb'] or 8) * 1e9)}
for m in res.get('measure', []):
    if m['version'] == 'after' and m['rss_gb']: stats[f"scripts/{m['audit']}.lean"] = {'seconds': m['seconds'], 'max_rss_bytes': int(m['rss_gb']*1e9)}
def est(a): s = stats.get(a, {}); return s.get('seconds', 120), s.get('max_rss_bytes', 8e9)
order = sorted([a for a in audits if a != 'scripts/refactor/audit_sorries.lean'], key=lambda a: -est(a)[0])
batches, cur, curt = [], [], 0.0
for a in order:
    t, _ = est(a)
    if cur and curt + t/6 > 720: batches.append(cur); cur, curt = [], 0.0
    cur.append(a); curt += t/6
if cur: batches.append(cur)
log(f'{len(batches)} audit batches')
driver = S/'run_batch.py'
driver.write_text('''import subprocess,sys,json,re,time,concurrent.futures as cf
audits=sys.argv[2:]; out=sys.argv[1]; mem={}
def run(a):
    t=time.time(); p=subprocess.run(['/usr/bin/time','-l','lake','env','lean',a],capture_output=True,text=True)
    m=re.search(r'(\\d+)\\s+maximum resident set size',p.stderr)
    return {'audit':a,'rc':p.returncode,'seconds':round(time.time()-t),'rss_gb':m and round(int(m.group(1))/1e9,2),'tail':(p.stdout+p.stderr)[-1500:]}
with cf.ThreadPoolExecutor(6) as ex: rs=list(ex.map(run,audits))
open(out,'w').write(json.dumps(rs,ensure_ascii=False,indent=1))
sys.exit(0 if all(r['rc']==0 for r in rs) else 1)
''')
for k, b in enumerate(batches):
    outp = S/f'run-batch-{k}.json'
    rc, out, dt = locked(MERGE, ['python3', str(driver), str(outp)] + b, 1500)
    rs = json.loads(outp.read_text()) if outp.exists() else []
    bad = [r['audit'] for r in rs if r['rc'] != 0]
    log(f'batch {k}: {len(b)} audits rc={rc} {dt:.0f}s failed={bad}')
    res.setdefault('audits', []).extend(rs); save()
    if rc != 0: log('STOP: audit failures'); sys.exit(1)
# 5. sorry の閉包
rc, rss, dt, out = timed_lean(MERGE, 'scripts/refactor/audit_sorries.lean', 1500)
ok = rc == 0 and 'sorry closure PASS' in out
log(f'sorry closure: rc={rc} {dt:.0f}s RSS={rss and rss/1e9:.1f}GB PASS={ok}')
res['sorry'] = {'rc': rc, 'seconds': round(dt), 'pass': ok, 'tail': out[-1500:]}; save()
if not ok: log('STOP: sorry closure failed'); sys.exit(1)
log(f"ALL AUDITS PASS: {len(res['audits'])} audits + sorry closure on {head}")
log('MERGE-CHECKS-DONE')
