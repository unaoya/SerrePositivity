# IF-W0-3 §7-1：93d84541e 再検査・停止報告

**結果：全体 verify は FAIL、gate:true、終了コード1。W1 の PASS 条件は未達。** 層検査・W1 JSON検査・手作業を含む模擬・ビルド2段は成功した。99監査は96成功・3失敗、sorry閉包の検査は読込時に失敗した。既存監査・環境を修正せず、再実行もしない。W2a の続行条件を満たさないため、§7-2 には進んでいない。

基準 `93d84541e07644e4b8d328dd788024bf29fb1703`。専用 worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3` で `git merge --ff-only main` を実施。main 作業木での作業・ビルドなし。新しいコミットは作成していない。

検査一式の開始 2026-10-29T23:31:27.395761+09:00、終了 2026-10-30T00:57:46.606827+09:00。準備したランナーは端末から独立させ、SIGHUP を無視してログを保存した。全体 verify の起動は1回だけ。

## コマンドと時間

```sh
git merge --ff-only main
python3 -B scripts/refactor/layer_check.py --report
python3 -B scripts/refactor/validate_targets.py scripts/refactor/targets/w1.json --snapshot MODULE=FILE ...
VERIFY_JOBS=3 VERIFY_CACHE=0 zsh scripts/refactor/verify.sh
```

snapshot 引数3件、模擬の全引数、各終了コードは `.lake/verify/ifw0-3-resume-93d84541e/state.json` に記録した。試験用入口は設定していない。runner の jobs=3、cache_enabled=false、キャッシュ命中0件を確認。

| 段 | 終了コード・結果 | 秒 |
| --- | --- | ---: |
| layers | 0 | 30.056 |
| validator | 0 | 32.072 |
| simulation | 0 | 44.093 |
| preparation / manifest-and-targets | 0 / success | 2.897 |
| build / root | 0 / success | 992.784 |
| build / audit-targets | 0 / success | 2217.992 |
| 99監査（3並列、実時間） | 96成功・3失敗 | 1649.262 |
| sorry 閉包 | 1 / 読込エラーで判定未到達 | 133.510 |
| verify 全体（summary.json） | 1 / FAIL | 5070.773 |
| 層・JSON・模擬を含む一式 | STOP | 5179.211 |

監査は並列なので、各監査の秒数の和は上表の実時間とは異なる。verify 全体には層レポート・依存情報の準備・集計などの時間も含む。

## summary.json

```json
{
  "status": "FAIL",
  "gate": true,
  "commit": "93d84541e07644e4b8d328dd788024bf29fb1703",
  "seconds": 5070.773,
  "audit_count": 99,
  "executed_audit_count": 99,
  "target_count": 6465,
  "counts": {
    "build": {
      "success": 2,
      "failure": 0,
      "known": 0
    },
    "audit": {
      "success": 96,
      "failure": 3,
      "known": 0
    },
    "sorry": {
      "success": 0,
      "failure": 1,
      "known": 0
    },
    "preparation": {
      "success": 1,
      "failure": 0,
      "known": 0
    }
  },
  "failures": [
    "audit: scripts/audit_axioms.lean (exit 1)",
    "audit: scripts/audit_derived_cell_projective.lean (exit 1)",
    "audit: scripts/audit_f5.lean (exit 1)",
    "sorry: scripts/refactor/audit_sorries.lean (exit 1)"
  ]
}
```

全量は `.lake/verify/ifw0-3-resume-93d84541e/verify-summary.json`。監査一覧99本、実行99本、ビルド対象6,465本。新規・欠落監査はなし。

## 失敗の署名・エラー先頭3行・理由

### scripts/audit_axioms.lean

終了コード 1、233.758秒。

`Too many open files in system` によるファイル読込失敗。該当 .ir は実行後に存在を確認した。システム全体の同時オープン数制限が原因候補。上限変更・他レーンの停止・再実行はしていない。

署名（summary の原文）：

```json
{
  "error_count": 1,
  "errors": [
    {
      "file": "scripts/audit_axioms.lean",
      "line": 2,
      "declaration": "<top-level>",
      "message": "failed to open file '/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/build/lib/lean/SerrePositivity/InfinityCategories/F1/Coherent/LeftIntervalWeightedSimplex.ir': Too many open files in system"
    }
  ]
}
```

ログ先頭3行（1行しかないログはその1行）：

```text
scripts/audit_axioms.lean:2:0: error: failed to open file '/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/build/lib/lean/SerrePositivity/InfinityCategories/F1/Coherent/LeftIntervalWeightedSimplex.ir': Too many open files in system
```

保存ログ：`.lake/verify/ifw0-3-resume-93d84541e/verify-audit-1b56d83cd10bef3b396a.log`。

### scripts/audit_derived_cell_projective.lean

終了コード 1、13.791秒。

Std.WP.Gadget.ForIn.olean がないという診断。ただし実行後には同じ絶対パスのファイルが存在（110,296 bytes）した。同じ実行中にファイル数制限のエラーが出ているため一時的な読込失敗が候補だが、同じ原因とは確定していない。

署名（summary の原文）：

```json
{
  "error_count": 1,
  "errors": [
    {
      "file": "scripts/audit_derived_cell_projective.lean",
      "line": 1,
      "declaration": "<top-level>",
      "message": "object file '/Users/sugakubunka/.elan/toolchains/leanprover--lean4---v4.35.0-rc4/lib/lean/Std/WP/Gadget/ForIn.olean' of module Std.WP.Gadget.ForIn does not exist"
    }
  ]
}
```

ログ先頭3行（1行しかないログはその1行）：

```text
scripts/audit_derived_cell_projective.lean:1:0: error: object file '/Users/sugakubunka/.elan/toolchains/leanprover--lean4---v4.35.0-rc4/lib/lean/Std/WP/Gadget/ForIn.olean' of module Std.WP.Gadget.ForIn does not exist
```

保存ログ：`.lake/verify/ifw0-3-resume-93d84541e/verify-audit-1dc49f7159416f000ac0.log`。

### scripts/audit_f5.lean

終了コード 1、12.980秒。

33行目が古い `isAdicComplete_regular_quotient_natCast_of_bounded_torsion` を参照している。現ソースの検索では監査以外に見つからない。Adic/BoundedTorsionQuotient.lean:40 には `isAdicComplete_principal_quotient_natCast_of_bounded_torsion` があり、正則性の2引数を要求しない。import の移転は解消したが、監査本文のAPI追従が残っていると判断。後続の No goals / contains sorry はこの証明の elaboration 失敗に伴う診断。変更していない。

署名（summary の原文）：

```json
{
  "error_count": 3,
  "errors": [
    {
      "file": "scripts/audit_f5.lean",
      "line": 33,
      "declaration": "theorem f5_audit_distinguished_quotient (D : DeltaStructure p A) (hD : D.IsPerfect)",
      "message": "Unknown identifier `isAdicComplete_regular_quotient_natCast_of_bounded_torsion`"
    },
    {
      "file": "scripts/audit_f5.lean",
      "line": 35,
      "declaration": "theorem f5_audit_distinguished_quotient (D : DeltaStructure p A) (hD : D.IsPerfect)",
      "message": "No goals to be solved"
    },
    {
      "file": "scripts/audit_f5.lean",
      "line": 51,
      "declaration": "theorem f5_audit_distinguished_power_quotient (D : DeltaStructure p A) (hD : D.IsPerfect)",
      "message": "SerrePositivity.BhattScholze.DeltaStructure.f5_audit_distinguished_quotient contains sorry"
    }
  ]
}
```

ログ先頭3行（1行しかないログはその1行）：

```text
scripts/audit_f5.lean:33:8: error(lean.unknownIdentifier): Unknown identifier `isAdicComplete_regular_quotient_natCast_of_bounded_torsion`
scripts/audit_f5.lean:35:2: error: No goals to be solved
scripts/audit_f5.lean:51:0: error: SerrePositivity.BhattScholze.DeltaStructure.f5_audit_distinguished_quotient contains sorry
```

保存ログ：`.lake/verify/ifw0-3-resume-93d84541e/verify-audit-f2f7d730459e700c37c1.log`。

### scripts/refactor/audit_sorries.lean

終了コード 1、133.510秒。

import 読込時の `Too many open files in system`。閉包の判定そのものに到達していないため、許可3件との一致や kanQuillen_model_exists の到達性は今回確認できていない。ソースへ sorry を追加したという診断ではない。

署名相当：sorry / import 時のファイル読込失敗 / Too many open files in system（summary は sorry の構造化署名を持たない）。

ログ先頭3行（1行しかないログはその1行）：

```text
scripts/refactor/audit_sorries.lean:1:0: error: failed to open file '/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/build/lib/lean/SerrePositivity/HomologicalAlgebra/GeneralLocalCohomologyBaseChange.olean.private': Too many open files in system
```

保存ログ：`.lake/verify/ifw0-3-resume-93d84541e/verify-sorry-2dcaaedabb04f90f7b6d.log`。

全ログを終端だけでなく全体で検索した。広い語検索の結果は `log-audit.json`、Lean診断行の抽出は `diagnostic-lines.json` に保存した。広い語検索には成功した監査の宣言名・出力も含まれるため、終了コードと診断形式を照合した。失敗は上記3監査とsorry段。ビルド2段にエラー診断なし。

途中の監視で最初の2監査の失敗を検出して停止を要求したが、停止コマンドが実行された時点では verify は自然終了済みだった。active_pid がなく、停止スクリプトは送信前の検査で終了したため SIGTERM は送っていない。今回の最終集計は中断値ではなく99監査完了後の値。

## 前回との数値比較

可換代数のF群再編によりグラフ全体は34モジュール・126辺減少。層の組ごとの違反・全 ratchet 指標・tier ごとの入口辺の集合・禁止閉包の件数は前回 cdbefbde9 と同一。

| 状態 | モジュール 前回 → 今回 | import辺 前回 → 今回 | 直接違反（今回、前回と同じ） |
| --- | ---: | ---: | ---: |
| before | 34042 → 34008 | 113620 → 113494 | 371 |
| targets | 34045 → 34011 | 113728 → 113602 | 325 |
| manual | 34040 → 34006 | 113713 → 113587 | 318 |

| tier | 元の禁止閉包 / 入口辺 | W1 JSON後 | 手作業込み |
| --- | ---: | ---: | ---: |
| W1 | 2986 / 32 | 1 / 3 | 1 / 3 |
| W2a | 3257 / 90 | 257 / 59 | 257 / 59 |
| W2b | 3257 / 90 | 257 / 59 | 257 / 59 |

| 層の組 | 元 | W1 JSON後 | 手作業込み |
| --- | ---: | ---: | ---: |
| F1 -> DGNerve | 1 | 0 | 0 |
| F1 -> Derived | 4 | 0 | 0 |
| F1 -> DoldKanComparison | 2 | 0 | 0 |
| F1 -> F2 | 28 | 17 | 10 |
| F1 -> SerrePositivity.HomotopicalAlgebra | 1 | 1 | 1 |
| F1 -> SerrePositivity.KST | 2 | 2 | 2 |
| F1 -> Stable | 23 | 23 | 23 |
| F1B -> Stable | 54 | 54 | 54 |
| F2 -> Derived | 7 | 3 | 3 |
| F2 -> SerrePositivity.HomotopicalAlgebra | 1 | 1 | 1 |
| F2 -> SerrePositivity.KST | 14 | 12 | 12 |
| HomotopyLimits -> DGNerve | 3 | 0 | 0 |
| HomotopyLimits -> Derived | 3 | 0 | 0 |
| HomotopyLimits -> DoldKanComparison | 2 | 0 | 0 |
| HomotopyLimits -> F2 | 84 | 82 | 82 |
| HomotopyLimits -> SerrePositivity.HomotopicalAlgebra | 14 | 14 | 14 |
| HomotopyLimits -> SerrePositivity.KST | 26 | 26 | 26 |
| HomotopyLimits -> Stable | 50 | 50 | 50 |
| Stable -> Derived | 10 | 0 | 0 |
| Stable -> F2 | 42 | 40 | 40 |

W1 の終了条件（中核の閉包に DG・EInfinity なし）はグラフ模擬上は達成。手作業込みで DG=0、EInfinity=0。W1 tier に残る1本は `Derived.CoherentBar.Compact.FilteredSpaceBridgeInput` で、既承認どおり W2b/R73 へ回す。これは層強制検査が完全に0という意味ではない。verify は FAIL のため、W1 の条件付き承認はまだ確定していない。

## 今回の変更と停止位置

- `scripts/refactor/targets/w1.json`：ルート reimport の一覧を今回の main に合わせ、旧可換代数26 importを外して新12 importを反映。W1による入口5件の追加は維持。他の67項目は変更なし。構成は move62・split3・reimport3。
- `scripts/refactor/targets/w1.md`：冒頭に今回の FAIL と本報告へのリンクを記録。
- `scripts/refactor/targets/w1-refresh-93d84541e-stop.md`：本報告。

その他の今回の生成物は `.lake/verify/ifw0-3-resume-93d84541e/` と verify 標準ログ。数学の Lean ソース・監査・道具は今回編集していない。既存の `decl_snapshot.lean` 等の差分は以前の作業を保持したもの。git diff --check は成功。

§7-1 の検査失敗として停止する。W2a は前回の `w2a-preflight-stop.md` の状態から変更していない。既存分割道具の attribute / 無名local instance の制約も未解決。全体 verify の2回目、既知失敗一覧への追加、コミットは行わない。

## 99監査の個別時間

| 監査 | 終了コード | 秒 |
| --- | ---: | ---: |
| `scripts/audit/adams.lean` | 0 | 63.849 |
| `scripts/audit/bhatt_scholze.lean` | 0 | 84.742 |
| `scripts/audit/clmst.lean` | 0 | 84.180 |
| `scripts/audit/dg.lean` | 0 | 84.544 |
| `scripts/audit/shared.lean` | 0 | 122.829 |
| `scripts/audit_adams_action_transport.lean` | 0 | 6.436 |
| `scripts/audit_andre_initial_coefficient.lean` | 0 | 11.918 |
| `scripts/audit_andre_unoriented.lean` | 0 | 13.098 |
| `scripts/audit_axioms.lean` | 1 | 233.758 |
| `scripts/audit_bhatt_scholze.lean` | 0 | 112.299 |
| `scripts/audit_bhatt_scholze_andre_conditional.lean` | 0 | 20.252 |
| `scripts/audit_bhatt_scholze_arc_excision.lean` | 0 | 23.464 |
| `scripts/audit_bhatt_scholze_b4.lean` | 0 | 18.777 |
| `scripts/audit_bhatt_scholze_b5.lean` | 0 | 14.846 |
| `scripts/audit_bhatt_scholze_prop813.lean` | 0 | 14.606 |
| `scripts/audit_bhatt_scholze_refactoring.lean` | 0 | 15.769 |
| `scripts/audit_clmst.lean` | 0 | 274.453 |
| `scripts/audit_clmst_b3.lean` | 0 | 22.707 |
| `scripts/audit_coherent_nerve.lean` | 0 | 21.678 |
| `scripts/audit_derived_cell_projective.lean` | 1 | 13.791 |
| `scripts/audit_derived_closure_functoriality.lean` | 0 | 61.350 |
| `scripts/audit_derived_coherent_bar.lean` | 0 | 22.125 |
| `scripts/audit_derived_coherent_bar_compact.lean` | 0 | 38.171 |
| `scripts/audit_derived_coherent_bar_retract.lean` | 0 | 12.714 |
| `scripts/audit_derived_coherent_bar_strict.lean` | 0 | 33.381 |
| `scripts/audit_derived_dg_nerve_reflection.lean` | 0 | 14.588 |
| `scripts/audit_derived_gluing.lean` | 0 | 57.511 |
| `scripts/audit_derived_infinity.lean` | 0 | 427.035 |
| `scripts/audit_derived_kappa_perfect.lean` | 0 | 33.467 |
| `scripts/audit_derived_native_family.lean` | 0 | 46.311 |
| `scripts/audit_derived_native_p.lean` | 0 | 38.139 |
| `scripts/audit_derived_sphere_closure.lean` | 0 | 34.961 |
| `scripts/audit_derived_suspension_coherent.lean` | 0 | 38.153 |
| `scripts/audit_derived_suspension_native.lean` | 0 | 34.983 |
| `scripts/audit_derived_suspension_replacement.lean` | 0 | 33.992 |
| `scripts/audit_dg_cell_comparison.lean` | 0 | 33.971 |
| `scripts/audit_dg_nerve.lean` | 0 | 13.338 |
| `scripts/audit_dg_perfect_projective_image.lean` | 0 | 9.176 |
| `scripts/audit_dg_projective_contraction.lean` | 0 | 8.273 |
| `scripts/audit_dg_quotient_parameter.lean` | 0 | 15.304 |
| `scripts/audit_dold_kan_comparison.lean` | 0 | 41.976 |
| `scripts/audit_einfinity.lean` | 0 | 159.603 |
| `scripts/audit_euler_betti_finite_support.lean` | 0 | 8.644 |
| `scripts/audit_euler_group_shared.lean` | 0 | 8.880 |
| `scripts/audit_exact_euler_finite_support.lean` | 0 | 7.869 |
| `scripts/audit_f2_compact.lean` | 0 | 21.469 |
| `scripts/audit_f2_idempotent.lean` | 0 | 18.398 |
| `scripts/audit_f2_ind.lean` | 0 | 28.886 |
| `scripts/audit_f2_pi_criterion.lean` | 0 | 19.352 |
| `scripts/audit_f4.lean` | 0 | 7.660 |
| `scripts/audit_f5.lean` | 1 | 12.980 |
| `scripts/audit_f6.lean` | 0 | 7.611 |
| `scripts/audit_f7.lean` | 0 | 11.793 |
| `scripts/audit_general_spectra.lean` | 0 | 7.911 |
| `scripts/audit_homotopical_foundations.lean` | 0 | 10.531 |
| `scripts/audit_homotopical_general_tools.lean` | 0 | 9.446 |
| `scripts/audit_homotopical_rectification.lean` | 0 | 12.397 |
| `scripts/audit_homotopy_cone_representative_shared.lean` | 0 | 8.294 |
| `scripts/audit_homotopy_limits.lean` | 0 | 58.120 |
| `scripts/audit_homotopy_property_shared.lean` | 0 | 6.775 |
| `scripts/audit_infinity_accessible_pullback.lean` | 0 | 28.372 |
| `scripts/audit_infinity_core.lean` | 0 | 43.540 |
| `scripts/audit_infinity_core_supply_s1_closed_stable.lean` | 0 | 22.308 |
| `scripts/audit_infinity_core_supply_s1_triangle.lean` | 0 | 7.064 |
| `scripts/audit_infinity_f1.lean` | 0 | 489.351 |
| `scripts/audit_infinity_f1_f1b.lean` | 0 | 25.133 |
| `scripts/audit_infinity_f1b.lean` | 0 | 53.245 |
| `scripts/audit_infinity_f2.lean` | 0 | 58.927 |
| `scripts/audit_infinity_f2_exchange.lean` | 0 | 20.162 |
| `scripts/audit_infinity_presentable.lean` | 0 | 34.587 |
| `scripts/audit_infinity_presentable_duality.lean` | 0 | 24.749 |
| `scripts/audit_infinity_presentable_local_objects.lean` | 0 | 24.811 |
| `scripts/audit_infinity_presentable_localization.lean` | 0 | 26.965 |
| `scripts/audit_infinity_presentable_supply.lean` | 0 | 22.840 |
| `scripts/audit_infinity_stable.lean` | 0 | 411.477 |
| `scripts/audit_kst_cofinality.lean` | 0 | 32.122 |
| `scripts/audit_kst_comparison.lean` | 0 | 38.910 |
| `scripts/audit_kst_core_flag.lean` | 0 | 25.316 |
| `scripts/audit_kst_derived_blowup.lean` | 0 | 16.215 |
| `scripts/audit_kst_derived_geometry.lean` | 0 | 11.803 |
| `scripts/audit_kst_descent.lean` | 0 | 13.794 |
| `scripts/audit_kst_descent_main.lean` | 0 | 11.668 |
| `scripts/audit_kst_fibration.lean` | 0 | 67.034 |
| `scripts/audit_kst_fibration_relative.lean` | 0 | 18.088 |
| `scripts/audit_kst_nonconnective.lean` | 0 | 78.151 |
| `scripts/audit_kst_pro_excision.lean` | 0 | 58.082 |
| `scripts/audit_kst_s_construction.lean` | 0 | 109.535 |
| `scripts/audit_kst_s_construction_tail.lean` | 0 | 68.306 |
| `scripts/audit_kst_scheme_lemmas.lean` | 0 | 13.540 |
| `scripts/audit_kst_spectra.lean` | 0 | 28.431 |
| `scripts/audit_kst_spectra_d3.lean` | 0 | 20.304 |
| `scripts/audit_kst_spectra_d3tail.lean` | 0 | 23.099 |
| `scripts/audit_kst_spectra_s3.lean` | 0 | 54.404 |
| `scripts/audit_local_algebra.lean` | 0 | 10.425 |
| `scripts/audit_localizing_invariants.lean` | 0 | 85.828 |
| `scripts/audit_refactor_infinity.lean` | 0 | 7.792 |
| `scripts/audit_spectra.lean` | 0 | 9.764 |
| `scripts/audit_stage4_contract.lean` | 0 | 10.117 |
| `scripts/audit_triangulated_k0_shift_shared.lean` | 0 | 8.865 |
