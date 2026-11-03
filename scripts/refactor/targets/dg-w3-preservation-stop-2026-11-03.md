# DG-W3：下流 PASS 後の保存比較で STOP（2026-11-03）

本停止は DG-W3 §12 の代替規則で解消済み。最新結果は [停止点 3 の報告](dg-w3-final-report.md)。以下は停止時点の記録。

`infra/dg-w3`、起点 `b23296091`、Lean の検証済み HEAD `68cfec6e4`。

**下流は PASS。保存比較は STOP。停止点 3 の完了報告ではない。**

## 停止理由

`dg-codex-w3.md` §5-2 と IF-W0-3 §10.34 D の規則に従い停止する。
`Quotient/DerivedComparison/Filtration.lean:898` の `DGQuotient.complexColimitComparison` で、before にあった型クラス引数が after から消えている。`pp.explicit false` と `true` の双方で確認した。

```diff
  [Small.{u} J] [HasColimitsOfShape J (ModuleCat.{u} A)]
- [HasExactColimitsOfShape J (ModuleCat.{u} A)]
  (F : J ⥤ Complex A)
```

上は elaboration 後の型の差であり、Lean ソースの編集案ではない。元ソースの section variable は現在も 878–879 行にある。このファイルの起点からのソース差分は import 1 行（`Complexes.ExactColimits` → `Complexes.Perturbation`）だけで、宣言本体は変更していない。import 閉包の拡大後に引数の使用が変わったことまでは確認できるが、原因となった具体的な instance 選択は未特定。表示差や証明無関係性だけで同一と扱わず、修正は未適用。

| 宣言（同じ DGQuotient 名前空間） | 行 | 残った比較項目 | pp の確認 |
| --- | ---: | --- | --- |
| complexColimitComparison | 898 | 型・本体 | HasExactColimitsOfShape の引数が消失。STOP |
| complexColimitComparison_naturality | 907 | 型 | 当該定義を参照。false の型は当該クラス束縛子の表示名以外同形だが、依存する定義の不一致が残るため一括 PASS にしない |
| complexColimitComparison_ι | 903 | 型 | 同上 |

3 宣言の公理・属性は一致。宇宙引数の順序は u・v・w のまま。
[pp.explicit false の全差分](dg-w3-preservation-pp.diff)と [機械可読報告](dg-w3-preservation-stop-2026-11-03.json)を添付。before/after の false/true ログ、採取用 Lean、v3b snapshot は `.lake/verify/dg-w3/` に保存。pp の採取自体は全 4 回 exit 0（合計 58.631 秒、before の該当モジュールのキャッシュ確認を含む）。

## 完了した検証

- 内部 48 統合先は round 4 で PASS。内部保存比較は親への束ね・生成 proof の共有を個別照合し、未説明 0 として §10 に従い下流へ進んだ。
- 外からの import は 596 ファイル（本番等 559・Archive 37）、監査一覧は 6 本を更新。非 import 部分の不変性を確認した。Archive はビルド・snapshot・監査・集約の対象外。
- 下流 13,972 本を 507 根の閉包でカバーし、Paper 24 本、ルート、監査 import 先を含めた。
- 全体 snapshot：before 1,645 モジュール・23,703 行、after 1,085 モジュール・22,735 行。機械比較の 42 件中、38 件は親への帰属・生成 proof の共有として説明済み。残る 4 件（3 宣言）が上記。
- universe 重点 4 モジュールの通常宣言 15 件と、HomotopyCategory 重点 4 宣言は型ハッシュ一致。宇宙順序差を表示差として扱っていない。
- 下流の注釈処置 21 ファイル・44 箇所は v3b の型・本体・公理・属性が一致。private の imageDescRecovery も既存の v3b 関数で別に採取して一致。

| 下流 round | 結果 | 秒 | 新規 Built | 失敗モジュール数 |
| ---: | --- | ---: | ---: | ---: |
| 1 | FAIL | 3097.479 | 5108 | 8 |
| 2 | FAIL | 3532.221 | 4446 | 7 |
| 3 | FAIL | 442.155 | 150 | 4 |
| 4 | FAIL | 533.030 | 185 | 2 |
| 5 | PASS | 57.541 | 3 | 0 |

失敗モジュール一覧は JSON。各 round の間に限定再ビルドと処置対象の保存照合を行った。

## 処置一覧（§11 の記録）

補充 import 0。内部を含め、完全修飾 14・束縛子の型 1・宇宙 1・局所 instance 20・heartbeat 設定 11 箇所。下流処置は 4 個の別コミット「下流の修飾・heartbeat」に記録した。heartbeat は D8 の候補。

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

この後に追加するコミットは本停止報告と pp 差分のみ。

## 保留と再開時の注意

- `layers.json` の PerfectComplex 例外 3 辺の削除、README の 126 統合先の表の適用、verify は未実施。草案・実行補助は証跡側に保持した。verify の既存 summary は本束の結果として使わない。
- STOP 確認後の Lean 修正・追加ビルドは行っていない。main の変更・ビルド・merge、rsync、∞ 所有の道具の変更はない。Lake キャッシュ 3 変数と共有鍵を使用した。
- before scratch は未解決の照合のため保持（`SerrePositivity-dgw3-before`、`b23296091`、Lean ソース無変更）。解決後に削除する。W2 の scratch には触れていない。
- 再開には上記型差の扱い・修復方針が必要。保存一致を確認してから層・README・verify（JOBS=6、MEMORY_GB=40）へ進む。
