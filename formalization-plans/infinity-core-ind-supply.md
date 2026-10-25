# Ind-S 供給計画 v3

## 引き継ぎ（2026-10-25 14:12 JST）

- 所有：F1/・F1B/・Core/ の新規の葉と、対応する三監査スクリプトの末尾追記。
- 既存の深層ファイルは編集しない。F2/ は読み取り専用。K-B・Sp は import しない。
- 順序：(5) の供給、続いて (4) の順方向。計画正本は本ファイル。
  `infinity-core-F1.md` は Ind 所有なので編集しない。
- (5)：`d4062a19f` で L3 指定型の全族写像・厳密な底・全 fiber 回収を供給済み。
  同じ写像について指定点の値照合から fiber 内の頂点同型を反映する公開補題も供給済み。
  K-B 所有の具体的な恒等点への代入は未検証であり、K-B-S 全体の完成とは数えない。
- (4)：`5686de2be` で小さい内ホーン閉包、小さい quasicategory 模型、
  同じ包含への全小図式の厳密因子化を保存済み。局所化の宇宙持ち上げは未証明。
- (4) の追加：指定辺族の逆三角形を含む小模型と反転条件を保つ厳密因子化がビルド済み。
  `IsLocalization.exists_extension_ulift` で任意の大きい標的への実延長もビルド済み。
- 次：大きい標的に対する前合成の充満忠実性。境界資料と可逆 path を同じ小模型へ因子化する。
- 停止条件は foundations §8 に従う。ビルド失敗だけで停止しない。
  以後のコミット本文には変更・検証・残件の実施記録を書く。

## 所有と依存

- 新規葉は既存の Core/F1/F1B 公開界面を使う。既存モジュールへの逆流を作らない。
- 許可済み逆方向 import：D の `Derived.FunctorIsoConstantEdges`・
  `PinchedSliceCompositionRealization`・`ConstantEdgeFamily` を閉包外の新規 F1 葉から
  読み取り専用で利用可。第 I 段終了時に R が整理する。
- Ind に許可済みの `Stable.PosetSubtypeNerve`・`Stable.FinitePosetNerve` は
  読み取り専用の供給経路。今回の (4)/(5) の追加葉では未使用。
- (4) は no-straightening を守る。`Stable.UniverseVertexIso` は直接 import 不可。
  軽量な準重複 `Core.UniverseEdgeTransport` の `UniverseEdge.invertible_up/down` を使う。
- P の `nerveOrderIso`・`spaceUniverseDiagram...` は F2 を含む閉包の循環により不可。
- 追加の ModelCategory 仮定・供給結論そのものの存在仮定・新公理は導入しない。

## (5) 三段目と公開界面

1. [x] 相対関手空間で scaffold 全族を降下し、重み付き Kan 単位を構成する。
2. [x] 同じ族を小さい空間値 unstraightening へ写し、底の厳密等号を保つ。
3. [x] 全ての底頂点で、同じ全族写像の fiber 制限を標準値回収により元の Kan 単位へ戻す。
4. [x] 同じ fiber 回収同型から、あらかじめ指定された点との値同型を頂点同型へ反映する。
   K-B の具体的な恒等点との値同型の代入・接続は K-B 側で未検証。
5. [x] L3 の要求型を Lean で再検査し、対象ビルド・葉公理監査・F1 全監査を通して保存する。

公開名（`SerrePositivity.InfinityCategories` 以下。正確な namespace は各葉参照）：

- `exists_cocartesianKanUnstraighteningUnit`
  (`F1/Diagrams/CocartesianKanUnstraighteningUnit`)。
  元の cocartesian fibration `p`、Kan 置換関手 `R`、単位 `η` から同じ `f` と
  `hf : f ≫ projection = p` を構成し、全ての `c` で
  `fiberMap(f,hf,c) ≫ canonicalValue ≫ R.map(evaluate p c)` と
  `η.app(vertexFiber p c)` の FunctorIso を供給する。
  本体には `η` の anodyne 性すら不要。
- `cocartesianKanUnstraighteningUnit_pointIso`
  (`F1/Diagrams/CocartesianKanUnstraighteningUnitPoints`)。
  `η` の anodyne 性のもと、上の同じ `f/hf` と fiber 回収同型を入力し、
  指定点 `v` の標準値と元の点 `x` の Kan 単位値の VertexIso から
  `VertexIso (fiberMap(f,hf,c)(x)) v` を返す。点を選び直さない。
- `cocartesianKanUnitEvaluation_isQCatEquivalence`：点反映に使う評価比較の同値性。
- `relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization`：
  追加の相対初頂点補題（`5221e4db3`、既に K-B 消費済み）。

検証済み：最終対象ビルド、L3 指定型の直接適用例、公開主定理の公理、
最終追加葉 35 宣言の公理監査、F1 全監査。許容公理は propext・Classical.choice・Quot.sound。
残り：K-B 所有の `weakIdentityQuotientFiberPoint` 等を同じ全族写像に代入する消費側接続。
この残件を一般 F1 の不足と混同しない。

## (4) 順方向の三段目と公開界面

1. [x] 小さい像・小さい和と、有限単体集合の像が増大列の一段に入る補題。
2. [x] ambient quasicategory 内で小さい内ホーン充填閉包を構成する。
3. [x] 閉包を小さい quasicategory に縮小し、同じ包含で全小図式を厳密因子化する。
4. [x] 逆辺と二つの逆三角形を種に追加し、指定可逆辺を保存する小模型を作る。
5. [ ] 大きい標的への局所化延長と、全前合成の充満忠実性を小模型から回収する。
   延長成分は `IsLocalization.exists_extension_ulift` でビルド済み。充満忠実性が残る。
6. [ ] `IsLocalization` の ULift 持ち上げと既存降下を合わせた iff を公開し、監査・保存する。

保存済みの公開名（namespace `SerrePositivity.InfinityCategories.SmallSubcomplex`）：

- `small_range`・`small_iSup`・`exists_range_le_stage`
  (`Core/SmallSubcomplexStages`)。
- `innerHornClosure`・`le_innerHornClosure`・`small_innerHornClosure`・
  `innerHornClosure_quasicategory` (`Core/SmallInnerHornClosure`)。
- `model`・`modelIso`・`model_quasicategory` (`Core/SmallSimplicialModel`)。
- `Hull`・`hull` (`Core/SmallQuasicategoryHull`)。
  `Hull.factor` は `range f ≤ seed` を満たす任意の持ち上げた小さい源の図式を、
  同じ小模型と同じ包含に対して厳密に因子化する。

既存の供給済み降下：`IsLocalization.of_ulift`・`invertsEdges_ulift_iff`
(`F1B/Localization/UniverseDescent`)。
現在の小模型だけでは ambient での可逆性を反映しないため、段目 4 は必要。
順方向の公開名はまだない。対象ビルドと追加 Core 4 葉の 72 宣言公理監査は通過済み。

段目 4〜5 の追加公開名：

- `inverseWitnessSeed`・`small_inverseWitnessSeed`・`inverseWitnessSeed_reflects_edge`
  (`Core/SmallInverseWitnessSeed`)：同じ逆辺と二つの実三角形を保持する。
- `markedHull`・`markedHull_reflects_edge` (`Core/SmallMarkedQuasicategoryHull`)。
- `exists_small_inverting_factorization` (`F1B/Localization/SmallMarkedFactorization`)：
  元の持ち上げた図式を厳密に因子化し、指定辺の反転を保持する。
- `LocalizationUniverse.functorIso_ulift` (`F1B/Localization/UniverseMorphismUp`)：
  同じ実関手同型を持ち上げる軽量入口。
- `IsLocalization.exists_extension_ulift` (`F1B/Localization/UniverseExtension`)：
  任意の大きい quasicategory を標的とする反転関手の実延長。
- `LocalizationUniverse.fullyFaithful_ulift`・`precomposition_fullyFaithful_ulift_target`
  (`F1B/Localization/UniverseFaithfulUp`)：小さい標的を持ち上げた場合の充満忠実性。
- `isFullyFaithful_of_positive_boundary`
  (`F1B/FunctorCategories/PositiveBoundaryFaithful`)：正次元境界の持ち上げからの判定。

追加の Core 二葉 14 宣言、延長三葉 11 宣言の公理・no-straightening 監査通過。
Core 全監査、F1B 全監査（延長三葉まで）も通過。最終の充満忠実性と iff は未供給。
