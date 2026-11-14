#!/bin/zsh
# 概要：ビルド・全監査・sorry 閉包をまとめて合否を判定する。
# 方針：失敗を保存して集計し、既知の監査失敗だけを署名の完全一致で除外する。
# 規約：専用 worktree で実行する。生成物は .lake/verify、ログは verify.log。
# 使われ方：README.md の基準実行と検収に用いる。
set -o pipefail
cd "$(dirname "$0")/../.." || exit 1
zmodload zsh/datetime || exit 1
export LC_ALL=C
LOG=scripts/refactor/verify.log
OUT=.lake/verify
mkdir -p "$OUT" || exit 1
started=$EPOCHREALTIME
export VERIFY_STARTED=$started
: > "$OUT/stages.tsv" || exit 1
print -r -- "=== verify $(date '+%F %T') HEAD $(git rev-parse HEAD)" | tee -a "$LOG"

# Capture every pipeline status immediately; never let filtering hide the command status.
run_stage() {
  local kind=$1 label=$2
  shift 2
  local begin=$EPOCHREALTIME
  local -a codes
  local output="$OUT/${kind}-${stage_index}.log"
  print -r -- "--- $kind $label" | tee -a "$LOG"
  "$@" 2>&1 | tee "$output" >> "$LOG"
  codes=("${pipestatus[@]}")
  local rc=${codes[1]}
  if (( codes[2] != 0 )); then rc=1; fi
  local elapsed=$(( EPOCHREALTIME - begin ))
  printf '%s\t%s\t%s\t%.3f\t%s\n' "$kind" "$label" "$rc" "$elapsed" "$output" >> "$OUT/stages.tsv"
  print -r -- "$kind $label rc=$rc ${elapsed}s" | tee -a "$LOG"
  (( stage_index += 1 ))
  return $rc
}
integer stage_index=0
rm -f "$OUT/runner.json" "$OUT/audit-progress.json"
# Layer diagnostics are report-only until the coordinator enables enforcement.
python3 scripts/refactor/layer_check.py --report > "$OUT/layers.log" 2>&1
layer_rc=$?
printf '%s\n' "$layer_rc" > "$OUT/layers-exit-code.txt"
cat "$OUT/layers.log" >> "$LOG"
print -r -- "layer report rc=$layer_rc (informational; $OUT/layers.json)" | tee -a "$LOG"
run_stage preparation manifest-and-targets python3 - <<'PY'
import json, os, re, sys, time
from pathlib import Path
sys.path.insert(0, "scripts/refactor")
from audit_imports import audit_build_targets
out = Path('.lake/verify')
prep = {'errors': [], 'new_audits': [], 'missing_audits': [], 'audit_count': 0}
try:
    # Preserve the original orphan cleanup, including companion artifacts.
    base = Path('.lake/build/lib/lean/SerrePositivity')
    removed = 0
    for olean in base.rglob('*.olean'):
        rel = olean.relative_to(base).with_suffix('.lean')
        if not (Path('SerrePositivity') / rel).exists():
            stem = str(olean)[:-6]
            for ext in ['.olean','.olean.hash','.olean.private','.olean.private.hash',
                        '.olean.server','.olean.server.hash','.ilean','.ilean.hash',
                        '.trace','.ir','.ir.hash','.ir.sig','.ir.sig.hash','.c','.c.hash']:
                Path(stem + ext).unlink(missing_ok=True)
            removed += 1
    print(f'removed orphan modules: {removed}')
    audits = sorted(str(p) for p in Path('scripts').glob('audit_*.lean'))
    audits += sorted(str(p) for p in Path('scripts/audit').rglob('*.lean'))
    audits = sorted(audits)
    prep['audit_count'] = len(audits)
    manifest = [s.strip() for s in Path('scripts/refactor/audit_manifest.txt').read_text().splitlines()
                if s.strip() and not s.startswith('#')]
    if len(manifest) != len(set(manifest)):
        prep['errors'].append('duplicate audit manifest entries')
    prep['missing_audits'] = sorted(set(manifest) - set(audits))
    prep['new_audits'] = sorted(set(audits) - set(manifest))
    for path in prep['missing_audits']:
        prep['errors'].append(f'manifest audit missing: {path}')
    for path in prep['new_audits']:
        print(f'一覧への追加が必要: {path}')
    # 99 is the initial manifest size, not a permanent cap on future audits.
    extra = os.environ.get('VERIFY_EXTRA_AUDITS', '').split()
    audits = list(dict.fromkeys(audits + extra))
    prep['all_audits'] = audits[:]
    if 'VERIFY_ONLY_AUDITS' in os.environ:
        selected = os.environ['VERIFY_ONLY_AUDITS'].split()
        if not selected or len(selected) != len(set(selected)):
            prep['errors'].append('VERIFY_ONLY_AUDITS must be a nonempty unique list')
        for path in sorted(set(selected)-set(audits)):
            prep['errors'].append('selected audit not in manifest discovery/extras: '+path)
        audits = sorted(set(audits)&set(selected))
    jobs = os.environ.get('VERIFY_JOBS', '6')
    if not jobs.isdigit() or int(jobs) < 1:
        prep['errors'].append('VERIFY_JOBS must be a positive integer')
    import math
    try:
        memory = float(os.environ.get('VERIFY_MEMORY_GB', '45'))
        if not math.isfinite(memory) or memory < 0: raise ValueError()
    except ValueError:
        prep['errors'].append('VERIFY_MEMORY_GB must be finite and nonnegative')
    if os.environ.get('VERIFY_CACHE', '0') not in ('0','1'):
        prep['errors'].append('VERIFY_CACHE must be 0 or 1')
    prep['executed_audit_count'] = len(audits)
    (out / 'audits.txt').write_text(''.join(p + '\n' for p in audits))
    # Runtime importModules literals must be built even on a clean checkout.
    targets = audit_build_targets(Path(path).read_text() for path in audits)
    prep['target_count'] = len(targets)
    (out / 'audit_targets.txt').write_text(''.join(t + '\n' for t in sorted(targets)))
    print(f'audits: {prep["audit_count"]}; with extras: {len(audits)}; build targets: {len(targets)}')
except Exception as exc:
    prep['errors'].append(str(exc))
(out / 'preparation.json').write_text(json.dumps(prep, ensure_ascii=False, indent=2) + '\n')
for error in prep['errors']:
    print('error: ' + error)
raise SystemExit(bool(prep['errors']))
PY
prep_rc=$?
if (( prep_rc == 0 )); then
  if [[ ${VERIFY_SKIP_BUILD:-0} != 1 ]]; then
    run_stage build root lake build SerrePositivity
    targets=("${(@f)$(< "$OUT/audit_targets.txt")}")
    if (( ${#targets} )); then
      run_stage build audit-targets lake build "${targets[@]}"
    fi
  fi
  python3 scripts/refactor/verify_runner.py
  runner_rc=$?
  if (( runner_rc != 0 )); then
    run_stage preparation audit-runner-failed false
  fi
fi

python3 - <<'PY' | tee -a "$LOG"
import json, os, re, subprocess, time
from pathlib import Path
out = Path('.lake/verify')
prep = json.loads((out / 'preparation.json').read_text())
failures = list(prep['errors'])
baseline = {}
baseline_path = Path(os.environ.get('VERIFY_BASELINE', 'scripts/refactor/verify_baseline.txt'))
try:
    for i, line in enumerate(baseline_path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith('#'):
            continue
        path, commit, signature, reason = line.split('\t')
        sig = json.loads(signature)
        if path in baseline or not re.fullmatch(r'[0-9a-f]{40}', commit) or not reason.strip():
            raise ValueError(f'invalid/duplicate entry on line {i}')
        if set(sig) != {'error_count', 'errors'} or sig['error_count'] != len(sig['errors']) or not sig['errors']:
            raise ValueError(f'invalid signature on line {i}')
        baseline[path] = sig
except Exception as exc:
    failures.append(f'baseline error: {exc}')

ansi = re.compile(r'\x1b\[[0-9;]*[A-Za-z]')
def normalize(s):
    return ' '.join(ansi.sub('', s).split())

def declaration(path, line):
    """Include the source command/name; unnamed commands retain their source text."""
    try:
        lines = Path(path).read_text().splitlines()
    except OSError:
        return '<unknown>'
    for text in reversed(lines[:line]):
        if re.match(r'^\s*(?:#(?:print|check|eval|guard|assert)|(?:private\s+|public\s+|noncomputable\s+|unsafe\s+)*(?:theorem|lemma|def|opaque|axiom|example|instance)\b)', text):
            return normalize(text)
    return '<top-level>'

def signature(text):
    lines = ansi.sub('', text).splitlines()
    errors = []
    excerpts = []
    for i, line in enumerate(lines):
        m = re.match(r'^(.*?):(\d+):(\d+): error(?:\([^)]*\))?:\s*(.*)$', line)
        if not m:
            continue
        path = m[1]
        try:
            path = str(Path(path).resolve().relative_to(Path.cwd()))
        except ValueError:
            pass
        message = m[4]
        if not message.strip() and i + 1 < len(lines):
            message = lines[i + 1]
        errors.append({'file': path, 'line': int(m[2]),
                       'declaration': declaration(path, int(m[2])), 'message': normalize(message)})
        excerpts.append(lines[i:i+3])
    return {'error_count': len(errors), 'errors': errors}, excerpts

counts = {k: {'success': 0, 'failure': 0, 'known': 0} for k in ('build', 'audit', 'sorry', 'preparation')}
records = []
runner = json.loads((out / 'runner.json').read_text()) if (out / 'runner.json').exists() else {}
runner_records = {(r['kind'], r['name']): r for r in runner.get('stages', [])}
for row in (out / 'stages.tsv').read_text().splitlines():
    kind, label, rc, duration, logfile = row.split('\t')
    rc = int(rc)
    record = {'kind': kind, 'name': label, 'exit_code': rc, 'seconds': float(duration), 'log': logfile}
    if (kind,label) in runner_records:
        record.update({k: runner_records[(kind,label)][k] for k in ('cached','cache_key','retried','retry_reason','attempts','max_rss_bytes','measured_at','time_log')})
    state = 'success' if rc == 0 else 'failure'
    if kind == 'audit':
        if rc:
            text = Path(logfile).read_text(errors='replace')
            sig, excerpts = signature(text)
            record['signature'] = sig
            record['error_first_three_lines'] = excerpts
            # An unparsed process/tool error must never become an approved failure.
            unparsed = [line for line in text.splitlines()
                        if re.search(r'(^|\s)(?:error:|fatal error:)', line)
                        and not re.match(r'^.*?:\d+:\d+: error(?:\([^)]*\))?:', line)]
            if sig['error_count'] and not unparsed and baseline.get(label) == sig:
                state = 'known'
            print(f'{state.upper()}: {label} signature=' + json.dumps(sig, ensure_ascii=False, separators=(',', ':')))
            for excerpt in excerpts:
                print('\n'.join(excerpt))
            if not excerpts:
                print('\n'.join(text.splitlines()[:3]))
        elif label in baseline:
            print(f'一覧から外せる: {label}')
    record['result'] = state
    counts[kind][state] += 1
    if state == 'failure':
        failures.append(f'{kind}: {label} (exit {rc})')
    records.append(record)
executed = {r['name'] for r in records if r['kind'] == 'audit'}
if not prep['errors']:
    expected = set((out / 'audits.txt').read_text().splitlines())
    for path in sorted(expected - executed):
        failures.append('selected audit not executed: ' + path)
    if len([r for r in records if r['kind'] == 'audit']) != len(expected) or executed != expected:
        failures.append('audit execution set/count mismatch')
    if len([r for r in records if r['kind'] == 'sorry']) != 1:
        failures.append('sorry closure stage not executed exactly once')
excluded = set(prep.get('all_audits', [])) - set((out / 'audits.txt').read_text().splitlines())
for path in baseline.keys() - executed - excluded:
    failures.append(f'baseline audit not executed: {path}')
# Any explicitly set test hook is non-gate, including sorry-closure overrides.
hooks = ('VERIFY_EXTRA_AUDITS', 'VERIFY_SKIP_BUILD', 'VERIFY_BASELINE', 'SORRY_AUDIT_ROOT', 'SORRY_AUDIT_ALLOWED', 'VERIFY_ONLY_AUDITS')
gate = not any(k in os.environ for k in hooks) and os.environ.get('VERIFY_CACHE','0') != '1'
retried = sum(bool(r.get('retried')) for r in records)
status = 'FAIL' if failures else 'PASS'
summary_line = status + ('' if gate else ' (non-gate)') + ' ' + ' '.join(
    f'{k}(success={v["success"]},failure={v["failure"]},known={v["known"]})' for k,v in counts.items())
summary_line += f' retried={retried}'
try:
    layer_rc = int((out / 'layers-exit-code.txt').read_text())
    layer_report = {'exit_code': layer_rc, 'informational': True,
                    'report': json.loads((out / 'layers.json').read_text()) if layer_rc == 0 else None}
except (OSError, ValueError) as exc:
    layer_report = {'informational': True, 'error': str(exc)}
summary = {'status': status, 'gate': gate, 'summary': summary_line, 'retried': retried,
           'commit': subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip(),
           'seconds': round(time.time() - float(os.environ['VERIFY_STARTED']), 3),
           'audit_count': prep['audit_count'], 'target_count': prep.get('target_count', 0),
           'counts': counts, 'failures': failures, 'new_audits': prep['new_audits'], 'stages': records,
           'layer_check': layer_report, 'runner': runner,
           'executed_audit_count': prep.get('executed_audit_count', 0)}
(out / 'summary.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n')
print(f'total: {summary["seconds"]}s')
for failure in failures:
    print('failure: ' + failure)
print(summary_line)
raise SystemExit(bool(failures))
PY
codes=("${pipestatus[@]}")
(( codes[1] == 0 && codes[2] == 0 )) || exit 1
exit 0
