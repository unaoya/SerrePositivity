#!/bin/zsh
# 概要：リファクタ取り込み時の検証。監査スクリプトが import する全モジュールをビルドし、全監査と sorry 閉包監査を実行する。
# 方針：ルートの全体ビルドだけでは F2・HomotopyLimits・KST の集約外モジュールが再ビルドされないため、監査対象を明示的にビルドする。
# 規約：他の lake build と同時に走らせない（olean の競合を避ける）。結果は scripts/refactor/verify.log に追記。
# 　　　実行前に、ソースの無い古い olean（移動・削除済みモジュール）を .lake/build から除く（古い宣言の二重読込を防ぐ）。
# 使われ方：R レーンまたはコーディネータが main の取り込み前後に実行する。
set -o pipefail
cd "$(dirname "$0")/../.."
LOG=scripts/refactor/verify.log
echo "=== verify $(date '+%F %T') HEAD $(git rev-parse --short HEAD)" | tee -a $LOG
echo "--- remove orphan oleans (modules without source)" | tee -a $LOG
python3 - <<'PY' | tee -a $LOG
import os
B='.lake/build/lib/lean/SerrePositivity'; S='SerrePositivity'; n=0
for root,_,files in os.walk(B):
    for fn in files:
        if fn.endswith('.olean'):
            rel=os.path.relpath(os.path.join(root,fn),B)[:-6]
            if not os.path.exists(os.path.join(S,rel+'.lean')):
                base=os.path.join(root,fn[:-6])
                for ext in ['.olean','.olean.hash','.olean.private','.olean.private.hash','.olean.server','.olean.server.hash','.ilean','.ilean.hash','.trace','.ir','.ir.hash','.ir.sig','.ir.sig.hash','.c','.c.hash']:
                    f=base+ext
                    if os.path.exists(f): os.remove(f)
                n+=1
print(f'removed orphan modules: {n}')
PY
echo "--- lake build SerrePositivity" | tee -a $LOG
lake build SerrePositivity 2>&1 | grep -E 'error|✖|Build completed' | tail -20 | tee -a $LOG
# 監査対象は実行時に監査スクリプトの import 行から集める（移動後の所在に追随する）。
grep -hE '^import SerrePositivity' scripts/audit_*.lean | sed 's/^import //' | sort -u > scripts/refactor/audit_targets.txt
echo "--- lake build <audit targets> ($(wc -l < scripts/refactor/audit_targets.txt | tr -d ' ') modules, derived from scripts/audit_*.lean)" | tee -a $LOG
lake build $(tr '\n' ' ' < scripts/refactor/audit_targets.txt) 2>&1 | grep -E '^error|✖|Build completed|^- SerrePositivity' | tail -60 | tee -a $LOG
echo "--- audits" | tee -a $LOG
for a in audit_infinity_core audit_infinity_f1 audit_infinity_f1b audit_infinity_f1_f1b audit_infinity_f2 audit_f2_ind audit_f2_compact audit_f2_idempotent audit_infinity_presentable audit_homotopy_limits audit_infinity_stable audit_derived_infinity audit_derived_gluing audit_dg_nerve audit_coherent_nerve audit_dold_kan_comparison audit_einfinity audit_kst_fibration audit_kst_s_construction audit_localizing_invariants audit_kst_nonconnective audit_kst_spectra audit_spectra audit_refactor_infinity; do
  s=$(date +%s); out=$(lake env lean scripts/$a.lean 2>&1); rc=$?
  echo "$a rc=$rc $(( $(date +%s) - s ))s" | tee -a $LOG
  [ $rc -ne 0 ] && echo "$out" | grep -m3 'error' | cut -c1-240 | tee -a $LOG
done
echo "--- sorry closure of main_statement" | tee -a $LOG
lake env lean scripts/refactor/audit_sorries.lean 2>&1 | tail -5 | tee -a $LOG
echo "=== end $(date '+%F %T')" | tee -a $LOG
