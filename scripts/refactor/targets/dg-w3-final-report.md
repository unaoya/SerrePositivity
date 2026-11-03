# DG-W3 停止点 3（停止点 2 を併記）

起点 `b23296091`、`infra/dg-w3`、専用 worktree `SerrePositivity-dgw1`。Lean の最終 HEAD は `6dc2abc1f`。
**下流・保存比較・層検査・verify は PASS、gate:true。** main の後続指示は `git show` で読み、main の merge・変更・ビルドは行っていない。

## 適用と受入確認

- D4：土台 5 ディレクトリ、608 元 → 48 統合先（承認済み private_renames 3 件）。D5：31 ファイル・224 docstring 参照を archive の目録へ。
- 事前 `--check --max-lines 1700`：48・608・最大 1,621 行、上限超過 0、統合先循環 0。601 件は従来の匿名 section 閉鎖の警告。
- universe コマンド列は 608/608 の元順序を各 section 内に保持。順序の回帰試験 PASS（22.436 秒）。
- 宣言到達性 16,084 組で失われる参照 0、DG の禁止依存 0。
- 外部付け替え：import だけの 596 ファイル（本番等 559・Archive 37）と監査 6 本。非 import 部分の不変性を確認。DG 監査を再生成。
- 追跡対象 Lean 31,431 本で、廃止した W3 モジュールへの import 0、欠落統合先 0。Archive はビルド・snapshot・監査・集約に含めていない。
- 下流は 13,972 本を 507 根の閉包でカバー。ルート SerrePositivity、監査の import 先、Paper 24 本を含む。

## ビルド round

| 内部 round | 結果 | 秒 | 失敗モジュール |
| ---: | --- | ---: | --- |
| 1 | FAIL | 37.440 | DifferentialGraded.Category.Basic |
| 2 | FAIL | 8.483 | DifferentialGraded.Functor.QuasiEquivalence |
| 3 | FAIL | 510.267 | DifferentialGraded.Tensor.ScalarExtension.BalancedTensor |
| 4 | PASS | 424.826 | なし |

| 下流 round | 結果 | 秒 | 新規 Built | 失敗モジュール数 |
| ---: | --- | ---: | ---: | ---: |
| 1 | FAIL | 3097.479 | 5108 | 8 |
| 2 | FAIL | 3532.221 | 4446 | 7 |
| 3 | FAIL | 442.155 | 150 | 4 |
| 4 | FAIL | 533.030 | 185 | 2 |
| 5 | PASS | 57.541 | 3 | 0 |

失敗箇所の限定再ビルドも別に記録した。

| 限定再ビルド | 結果 | 秒 | 失敗モジュール数 |
| ---: | --- | ---: | ---: |
| 1 | FAIL | 42.203 | 4 |
| 2 | FAIL | 40.942 | 3 |
| 3 | PASS | 38.597 | 0 |
| 4 | PASS | 13.018 | 0 |
| 5 | PASS | 14.293 | 0 |
| 6 | FAIL | 24.837 | 1 |
| 7 | PASS | 19.535 | 0 |

失敗モジュールの全一覧と round ごとの情報は [JSON](dg-w3-final-report.json)。補充の import は 0 件。

## 保存比較

before 1,645 モジュール・23,703 行、after 1,085 モジュール・22,735 行。規則は proof-irrelevant v3b。補充した before は `b23296091` の scratch を Lake キャッシュで復元して採取し、Lean ソースは変更していない。

機械比較の残り 42 件は個別照合し、未説明 0。38 件は全フィールドが同じ親への帰属差、および生成 proof の番号・共有の対応を照合した。残る 4 件は §12 の代替規則で仮定の脱落として説明済みにした（ハッシュ一致ではない。下記参照）。詳細は `.lake/verify/dg-w3/full-preservation-review.json`。

- 重点 universe 4 モジュールの通常宣言 15 件は型ハッシュ一致。notation 補助 36 件は既定の transient 規則で別記し、宇宙差を表示差として処理していない。
- DGNerve/HomotopyCategory の toH0・equivalence・fromH0・counitIso は型ハッシュ一致。追加の完全修飾は不要。
- 下流 21 ファイル・44 箇所は型・本体・公理・属性が一致。通常の採取器が除く private lemma imageDescRecovery も、既存の変更していない v3b 関数で個別採取して一致。最終個別採取は診断なし。
- 最終一括採取の 64 本の群で heartbeat 上限に達したため、成功済み 192 本を保持し、残りを 16 本以下に分けた。既存の採取器とハッシュ規則は変更していない。

## 修飾・型の明示・heartbeat の一覧

内部分を含め、完全修飾 14・束縛子の型 1・宇宙 1・局所 instance 20・heartbeat 設定 11 箇所。heartbeat 設定は D8 の調査候補。

| ファイル・行 | 処置 | 内容 |
| --- | --- | --- |
| [DifferentialGraded/Category/Basic:1005](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L1005) | 完全修飾 | `rw [he, _root_.CategoryTheory.Functor.map_id] at h` |
| [DifferentialGraded/Functor/QuasiEquivalence:268](../../../SerrePositivity/DifferentialGraded/Functor/QuasiEquivalence.lean#L268) | 束縛子の型の明示 | `(H : ∀ (x y : D), (x ⟶[Complex A] y) ⟶ (F x ⟶[Complex A] F y))` |
| [DifferentialGraded/Quotient/Scalar:310](../../../SerrePositivity/DifferentialGraded/Quotient/Scalar.lean#L310) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [DifferentialGraded/Quotient/Scalar:322](../../../SerrePositivity/DifferentialGraded/Quotient/Scalar.lean#L322) | 局所 instance（letI） | `letI : HasColimitsOfSize.{u, u} (Complex A') := ⟨fun _ _ => inferInstance⟩` |
| [DifferentialGraded/Tensor/ScalarExtension/BalancedTensor:396](../../../SerrePositivity/DifferentialGraded/Tensor/ScalarExtension/BalancedTensor.lean#L396) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/BarrattEccles/CarrierDiagramModel:125](../../../SerrePositivity/EInfinity/BarrattEccles/CarrierDiagramModel.lean#L125) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/CarrierDiagramModel:128](../../../SerrePositivity/EInfinity/BarrattEccles/CarrierDiagramModel.lean#L128) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/CarrierDiagramModel:146](../../../SerrePositivity/EInfinity/BarrattEccles/CarrierDiagramModel.lean#L146) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/CarrierDiagramModel:149](../../../SerrePositivity/EInfinity/BarrattEccles/CarrierDiagramModel.lean#L149) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/DiagramAcyclicity:45](../../../SerrePositivity/EInfinity/BarrattEccles/DiagramAcyclicity.lean#L45) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/BarrattEccles/FreeForgetHomEquivalence:43](../../../SerrePositivity/EInfinity/BarrattEccles/FreeForgetHomEquivalence.lean#L43) | 局所 instance（letI） | `letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/FreeForgetHomKan:33](../../../SerrePositivity/EInfinity/BarrattEccles/FreeForgetHomKan.lean#L33) | 局所 instance（letI） | `letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/Products:29](../../../SerrePositivity/EInfinity/BarrattEccles/Products.lean#L29) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/BarrattEccles/Products:30](../../../SerrePositivity/EInfinity/BarrattEccles/Products.lean#L30) | heartbeat | `maxHeartbeats 200000 → 400000` |
| [EInfinity/BarrattEccles/Products:36](../../../SerrePositivity/EInfinity/BarrattEccles/Products.lean#L36) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/Products:100](../../../SerrePositivity/EInfinity/BarrattEccles/Products.lean#L100) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/BarrattEccles/Products:107](../../../SerrePositivity/EInfinity/BarrattEccles/Products.lean#L107) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/NormalizedOriginalHomComparison:51](../../../SerrePositivity/EInfinity/ComplexLimits/NormalizedOriginalHomComparison.lean#L51) | 局所 instance（letI） | `letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/NormalizedProbeTensorFrame:33](../../../SerrePositivity/EInfinity/ComplexLimits/NormalizedProbeTensorFrame.lean#L33) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/ComplexLimits/NormalizedSimplexReedy:27](../../../SerrePositivity/EInfinity/ComplexLimits/NormalizedSimplexReedy.lean#L27) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/ComplexLimits/NormalizedSimplexTensorReedy:26](../../../SerrePositivity/EInfinity/ComplexLimits/NormalizedSimplexTensorReedy.lean#L26) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/ComplexLimits/RightFrames:92](../../../SerrePositivity/EInfinity/ComplexLimits/RightFrames.lean#L92) | 局所 instance（letI） | `letI : Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/RightFrames:96](../../../SerrePositivity/EInfinity/ComplexLimits/RightFrames.lean#L96) | 局所 instance（letI） | `letI : Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/RightSimplicialFrames:87](../../../SerrePositivity/EInfinity/ComplexLimits/RightSimplicialFrames.lean#L87) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/RightSimplicialFrames:90](../../../SerrePositivity/EInfinity/ComplexLimits/RightSimplicialFrames.lean#L90) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/RightSimplicialFrames:99](../../../SerrePositivity/EInfinity/ComplexLimits/RightSimplicialFrames.lean#L99) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/ComplexLimits/RightSimplicialFrames:103](../../../SerrePositivity/EInfinity/ComplexLimits/RightSimplicialFrames.lean#L103) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩` |
| [EInfinity/Operad/AlgebraDiagramSmallness:30](../../../SerrePositivity/EInfinity/Operad/AlgebraDiagramSmallness.lean#L30) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/Operad/AlgebraDiagramSmallness:44](../../../SerrePositivity/EInfinity/Operad/AlgebraDiagramSmallness.lean#L44) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [EInfinity/Operad/AlgebraSmallObject:56](../../../SerrePositivity/EInfinity/Operad/AlgebraSmallObject.lean#L56) | 局所 instance（letI） | `letI : HasCoproducts.{u} P.Algebra := fun J => (inferInstance : HasColimitsOfSize.{u, u} P.Algebra).has_colimits_of_shape (Discrete J)` |
| [InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality:47](../../../SerrePositivity/InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality.lean#L47) | 完全修飾 | `HomologicalComplex.ιTruncLE L e` |
| [InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality:48](../../../SerrePositivity/InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality.lean#L48) | 完全修飾 | `HomologicalComplex.ιTruncLE K e` |
| [InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality:53](../../../SerrePositivity/InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality.lean#L53) | 完全修飾 | `HomologicalComplex.ιTruncLE L e` |
| [InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality:55](../../../SerrePositivity/InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality.lean#L55) | 完全修飾 | `HomologicalComplex.ιTruncLE K e` |
| [InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality:58](../../../SerrePositivity/InfinityCategories/Derived/CoherentBar/Compact/TruncationHomologyNaturality.lean#L58) | 完全修飾 | `HomologicalComplex.ιTruncLE L e` |
| [InfinityCategories/Derived/MooreHomology:29](../../../SerrePositivity/InfinityCategories/Derived/MooreHomology.lean#L29) | 完全修飾 | `HomologicalComplex.quasiIsoAt_ιTruncLE K e` |
| [InfinityCategories/Derived/MooreHomology:32](../../../SerrePositivity/InfinityCategories/Derived/MooreHomology.lean#L32) | 完全修飾 | `HomologicalComplex.ιTruncLE K e` |
| [InfinityCategories/Derived/Semifree:60](../../../SerrePositivity/InfinityCategories/Derived/Semifree.lean#L60) | heartbeat | `synthInstance.maxHeartbeats 20000 → 40000` |
| [KST/Comparison/GrouplikeComparison:46](../../../SerrePositivity/KST/Comparison/GrouplikeComparison.lean#L46) | 宇宙の明示 | `SSet.stdSimplex.isTerminalObj₀.{u}` |
| [KST/LocalizingInvariants/DGAlgebraMultiplicativeReedyUnderlying:36](../../../SerrePositivity/KST/LocalizingInvariants/DGAlgebraMultiplicativeReedyUnderlying.lean#L36) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex R) := ⟨fun _ _ => inferInstance⟩` |
| [KST/LocalizingInvariants/DGAlgebraMultiplicativeReedyUnderlying:40](../../../SerrePositivity/KST/LocalizingInvariants/DGAlgebraMultiplicativeReedyUnderlying.lean#L40) | 局所 instance（letI） | `letI : HasLimitsOfSize.{u, u} (Complex R) := ⟨fun _ _ => inferInstance⟩` |
| [KST/SConstruction/DGModuleNaturalConeImage:41](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImage.lean#L41) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeInl_d` |
| [KST/SConstruction/DGModuleNaturalConeImageComparison:25](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImageComparison.lean#L25) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeInl` |
| [KST/SConstruction/DGModuleNaturalConeImageComparison:27](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImageComparison.lean#L27) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeInl` |
| [KST/SConstruction/DGModuleNaturalConeImageComparison:29](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImageComparison.lean#L29) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeComparison` |
| [KST/SConstruction/DGModuleNaturalConeImageComparison:69](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImageComparison.lean#L69) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeComparison` |
| [KST/SConstruction/DGModuleNaturalConeImageComparison:88](../../../SerrePositivity/KST/SConstruction/DGModuleNaturalConeImageComparison.lean#L88) | 完全修飾 | `SerrePositivity.InfinityCategories.dgModuleFunctorConeIso` |

## §12：include と残る 3 宣言の扱い

`6dc2abc1f`（include）：`Quotient/DerivedComparison/Filtration.lean` の section 変数を `hJ` と命名（879 行）し、`complexColimitComparison`・`_ι`・`_naturality` の直前（897・904・909 行）に `include hJ in` を追加した。宣言は現在 899・905・910 行。

小再ビルド 13.402 秒、snapshot 10.346 秒で成功。unusedSectionVars の注意は承認どおり許容。include を加えても、定義から落ちた HasExactColimitsOfShape 引数は復元されず、v3b の型 3 件・本体 1 件の差は残った。当該モジュール 199 行の意味フィールドは include 前後で同じ。

**§12 の代替規則を適用した。** pp.explicit false では、complexColimitComparison の型・本体は当該仮定を取り除くと空白以外完全一致。2 補題の型は束縛子名の差以外一致。before の仮定を保持した 3 つの主張へ after の宣言を適用する Lean 探針も exit 0。公理・属性・宇宙引数の順序は一致。これをハッシュ一致とは記録しない。

[include 後の pp 差分](dg-w3-include-pp.diff)。探針・snapshot・照合記録は `.lake/verify/dg-w3/include-*`、`implication-probe.lean/.log`。

**instance 探針は §12 の原因仮説をそのまま裏付けてはいない。** 一般の J に対して、local な exactness 仮定を置かない `#synth HasExactColimitsOfShape J (ModuleCat A)` は after で合成失敗。local な仮定を置けば before/after とも `hJ` が選ばれた。複体の `HasColimitsOfShape` は両環境とも Mathlib の `HomologicalComplex.instHasColimitsOfShape`（`Mathlib/Algebra/Homology/HomologicalComplexLimits.lean:173`）が供給する。したがって「新たな大域 HasExactColimitsOfShape instance が供給元」とは断定しない。仮定削除だけであることと含意は、上記 pp と Lean 探針で直接確認した。


## 層と一覧

- DG → PerfectComplex の例外 3 辺と対応する allowed_until_move 3 件を削除。Spectra の既存 allowed_until_move 2 件は保持。DG の直接違反 0。
- W1・W2a・W2b の各 core モジュール、および集計値で違反増加 0。全体の既存違反を新規の違反 0 と取り違えていない。

| 層 | 禁止モジュール（前→後） | 影響 core（前→後） | 閉包の組（前→後） | 直接違反（前→後） |
| --- | ---: | ---: | ---: | ---: |
| W1 | 1 → 1 | 11 → 11 | 11 → 11 | 3 → 3 |
| W2a | 166 → 166 | 3379 → 3379 | 316547 → 316547 | 28 → 28 |
| W2b | 166 → 166 | 3379 → 3379 | 316547 → 316547 | 294 → 294 |

[DG README の統合先 126 本の表](../../../SerrePositivity/DifferentialGraded/README.md#統合後の依存順)に、役割と DG 内の直接依存先・DAG の順位を記載。統合対象外の本番 37 本も別表に記載。ディレクトリ間には相互参照があるため、単純な内部 tier は登録していない。

## verify

`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`、共有鍵のもと、全監査を実行。`PASS`・`gate:true`、5561.170 秒、監査 100/100。

集計：`{"build": {"success": 2, "failure": 0, "known": 0}, "audit": {"success": 100, "failure": 0, "known": 0}, "sorry": {"success": 1, "failure": 0, "known": 0}, "preparation": {"success": 1, "failure": 0, "known": 0}}`。失敗 0、再試行 0。VERIFY_CACHE・ONLY・SKIP 等の省略フックは使用していない。

照合を終えた W3 scratch は、未コミット変更がないことを確認して削除済み。W2 scratch は保持。

全 Lake 実行で ~/.zshenv のキャッシュ 3 変数を使い、with_build_lock.sh で直列化した。rsync は使用していない。

## コミット

| コミット | 内容 |
| --- | --- |
| `244fb12fc` | docs(dg): record W3 preflight after paper layer 1-4 |
| `95b7756a1` | refactor(dg): D4 土台 — consolidate 608 modules into 48 |
| `ff39fe1d0` | docs(dg): D5 土台 — repoint module guides to archive |
| `03d5d350e` | fix(dg): 修飾 — retain CategoryTheory.Functor.map_id resolution |
| `3966182e8` | docs(dg): record W3 stop on inferred enriched object type |
| `2360dfd7b` | fix(dg): 修飾・型の明示 — preserve enriched object binders |
| `b89ea0f97` | fix(dg): heartbeat — bound scalar extension instance search locally |
| `ec057c5d8` | refactor(dg): retarget W3 consumers and audit inventories |
| `fa82b4857` | 下流の修飾・heartbeat |
| `7f282d8c4` | 下流の修飾・heartbeat — round 2 |
| `8080a8054` | 下流の修飾・heartbeat — round 3 |
| `68cfec6e4` | 下流の修飾・heartbeat — round 4 |
| `06f2cf626` | DG-W3: 下流 PASS と保存比較の型差を報告 |
| `6dc2abc1f` | include |

本報告と層・README の仕上げはこの後の文書・設定コミットに含める。検証した Lean ソースは上記 HEAD のもの。main への取り込みは行っていない。

証拠：`.lake/verify/dg-w3/`、verify 本体は `.lake/verify/summary.json` と各 stage のログ。
