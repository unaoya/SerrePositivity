# Ind-S 供給計画 v3

## 引き継ぎ（2026-10-25 18:13 JST）

- 所有：F1/・F1B/・Core/ の新規の葉と、対応する三監査スクリプトの末尾追記。
- 既存の深層ファイルは編集しない。F2/ は読み取り専用。K-B・Sp・EInfinity は import しない。
- 今回：(6) E2 向け弱変形による局所化源の移送。計画正本は本ファイル。
  `infinity-core-F1.md` は Ind 所有なので編集しない。
- (5)：`d4062a19f` で L3 指定型の全族写像・厳密な底・全 fiber 回収を供給済み。
  同じ写像について指定点の値照合から fiber 内の頂点同型を反映する公開補題も供給済み。
  K-B 所有の具体的な恒等点への代入は未検証であり、K-B-S 全体の完成とは数えない。
- (4)：`5686de2be` で内ホーン閉包と小模型、`14923a0d5` で指定逆三角形の保持と
  大きい標的への延長を保存済み。境界・可逆 path の同じ小模型への因子化を接続し、
  `IsLocalization.ulift`・`isLocalization_ulift_iff` まで対象ビルドが通過。
- 現在地：(6) 完了。本体・逆向き版の対象ビルド、要求型への直接適用、
  追加葉24宣言の公理・禁止仮定・禁止依存監査、Core/F1/F1B 三監査が全て通過。
- 主要宣言：`isLocalization_of_weakDeformation`・`isLocalization_of_weakDeformation_reverse`。
- 依存と提供：(6) は Core/F1B の既存公開界面のみを使用し、E2-S (6) へ供給する。
  他レーンの証明はコピーしない。既存 `isLocalization_of_deformation` は変更しない。
- 未コミット：なし。既知の問題：なし。
- 残り：(6) の供給残件なし。E2 の具体的な消費は E2 所有。
- 次の一手：公開名をユーザーへ報告し、二段目 (6) 完了の規約で停止する。
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
5. [x] 大きい標的への局所化延長と、全前合成の充満忠実性を小模型から回収する。
6. [x] `IsLocalization` の ULift 持ち上げと既存降下を合わせた iff を公開し、監査・保存する。

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
段目 3 の小模型だけでは ambient での可逆性を反映しないため、段目 4 を経由する。
最初の Core 4 葉の対象ビルドと 72 宣言公理監査は通過済み。

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
Core 全監査、F1B 全監査（延長三葉まで）も通過。

最終公開名（`F1B/Localization/UniverseAscent`）：

- `IsLocalization.precomposition_isFullyFaithful_ulift`：任意の大きい標的での全前合成の充満忠実性。
- `IsLocalization.ulift`：`IsLocalization F W` から
  `IsLocalization (SSet.uliftFunctor.map F) (ULift.up '' W)`。
- `isLocalization_ulift_iff`：上の持ち上げと元の局所化性の iff。

源・標的の quasicategory 性、ModelCategory、局所化の追加存在証明は仮定しない。
証明は `Core/SmallHullFactorization`・`EquivalencePathReplacementNaturality` と
`F1B/FunctorCategories/SmallTargetDiagrams`・`SmallTargetBoundary` の新規葉へ隔離。
元の正次元境界とその二関手族・可逆 path 族・底単体を同じ marked 小模型へ移し、
小さい標的での充填を元の正方形へ厳密に戻す。

最終検証：UniverseAscent 対象ビルド 1680 jobs、元の要求型の直接適用例と iff、
主定理の公理確認、最終 Core 8 宣言・F1B 13 宣言の葉監査、Core/F1B 全監査が通過。
追加閉包は no-straightening、許容公理は標準三つのみ。F1 全監査は (5) 保存時に通過済み。

## (6) 弱変形による局所化源の移送

1. [x] 規約・既存の変形局所化界面・要求型を確認する。
2. [x] 指定辺を保つ制限と、反転関手圏上の全変形同型を構成する。
3. [x] 相互逆の制限同値を既存局所化の前合成同値へ合成し、本体を公開する。
4. [x] 恒等射から合成への逆向き H・K の版を同じ葉で公開する。
5. [x] 対象ビルド・三監査・公開型・禁止仮定を検査し、本文記録付きで保存する。

要求：i : A ⟶ B、r : B ⟶ A が WA・WB を相互に保ち、
H : Homotopy (r ≫ i) (𝟙 B)、K : Homotopy (i ≫ r) (𝟙 A) の点辺が WB・WA に入るとき、
IsLocalization q WA → IsLocalization (r ≫ q) WB。H・K が逆向きの場合も供給する。
源・標的の quasicategory 性、ModelCategory、局所化の追加存在仮定を加えない。
配置：新規 `F1B/Localization/WeakDeformationSource`。no-straightening を維持する。

公開名（namespace `SerrePositivity.InfinityCategories`）：

- `isLocalization_of_weakDeformation`：合成から恒等射への H・K による移送。
- `isLocalization_of_weakDeformation_reverse`：恒等射から合成への H・K による移送。
- `WeakDeformationSource.restriction`・`restriction_ι`：反転関手全族の制限と厳密な包含照合。
- `WeakDeformationSource.restrictionEquivalence`：全関手同型を保持する相互逆の制限同値。

両主定理の引数は i・r・q・WA・WB・相互保存・H・K・点辺所属・hq。
A・B・D の quasicategory 性は仮定しない。逆向き版は元のホモトピーを逆転させず、
反転関手族上で作った全同型を逆にして同じ普遍性を使う。
追加葉は `DeformationLocalization` のみを import し、既存定理を変更しない。

検証：対象ビルド 1980 jobs、要求された両向きの型への直接適用、両主定理の公理確認、
葉24宣言の公理・禁止依存・公開型中の ModelCategory 検査、Core/F1/F1B 三監査が通過。
許容公理は propext・Classical.choice・Quot.sound のみ。F1B 監査登録は末尾追記のみ。
