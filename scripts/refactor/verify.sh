#!/bin/zsh
# 概要：リファクタ取り込み時の検証。監査スクリプトが import する全モジュールをビルドし、全監査と sorry 閉包監査を実行する。
# 方針：ルートの全体ビルドだけでは F2・HomotopyLimits・KST の集約外モジュールが再ビルドされないため、監査対象を明示的にビルドする。
# 規約：他の lake build と同時に走らせない（olean の競合を避ける）。結果は scripts/refactor/verify.log に追記。
# 使われ方：R レーンまたはコーディネータが main の取り込み前後に実行する。
set -o pipefail
cd "$(dirname "$0")/../.."
LOG=scripts/refactor/verify.log
echo "=== verify $(date '+%F %T') HEAD $(git rev-parse --short HEAD)" | tee -a $LOG
echo "--- lake build SerrePositivity" | tee -a $LOG
lake build SerrePositivity 2>&1 | grep -E 'error|✖|Build completed' | tail -20 | tee -a $LOG
echo "--- lake build <audit targets> ($(wc -l < scripts/refactor/audit_targets.txt | tr -d ' ') modules)" | tee -a $LOG
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
