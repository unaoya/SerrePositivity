# Ind-S 供給計画 v3

## 引き継ぎ（2026-10-26、Ind-S (9)・(9b) 着手）

- 所有：F1/・F1B/・Core/ の新規葉と三監査の末尾追記、本計画。
- 深層編集は禁止、F2 は読み取り専用、K-B・Sp・EInfinity は import しない。
  F1 の straightening は使用可。(8) の限定推移 import 例外は今回へ拡大しない。
- 今回：(9) 制御二胞体族と (9b) 因子分解三単体族。提供先は K-B。
- 現在地：固定全ホーンの可縮性・比較、指定三面の実全族、零骨格指定延長が対象ビルド通過。
- 主要補助宣言：tetrahedronFamilyExtensionSpace_compare・factorizationTetrahedronFamily_faces・
  innerHornFamily_lift_with_vertices。いずれも両主仕様全体の供給完了とは扱わない。
- 依存と提供：Core/F1/mathlib の既存界面を読み取り専用で使用。連絡・提案はユーザー経由。
- 未コミット：F1/Diagrams/ の今回の新規葉、本計画、F1 監査末尾。
- 既知の問題：(9) の厳密な全族回収、(9b) の末尾の全 native Hom 一致は未証明。
  後者は単なる長い辺の等式ではない。仕様型を保持して構成を進める。
- 残り：下記三段目 2〜5。見積りは制御全族の有限座標を確認した後に更新する。
- 次の一手：(9b) の有限 enriched 畳み込みを完成し、指定零骨格延長で全族へ戻す。
  (9) の厳密 retraction は引き続き未構成。
- 検証は自分の対象と監査だけ。set -o pipefail、保存は git commit --only。
  新規 sorry・公理・ModelCategory SSet 仮定を入れない。実施記録はコミット本文へ。
- 停止は二段目完了・設計変更提案・所有 import 閉包破損・24時間のみ。ビルド失敗では停止しない。

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

## (7) 内ホーン充填閉包の濃度評価

1. [x] 規約・既存の閉包・暫定型を確認する。
2. [x] 有限個の面でホーン写像を数え、充填一段の非退化単体数を評価する。
3. [x] 各既存 innerHornStage と可算和の既存 innerHornClosure の μ-small 性を証明する。
4. [x] 既存 model・canonical hull と、Small 仮定不要の有界 Hull の存在へ移す。
5. [x] 対象ビルド・公開型・公理・禁止依存・三監査を通し、実施記録付きで保存する。

仮定は正則 μ と ℵ₀ < μ。強極限性は仮定しない。非退化表示から各次数を評価し、
ホーンからの射を有限個の面の Yoneda 値へ単射に送る。充填像は次数ごとに有限で、
充填添字と全段階の可算和を正則性で評価する。既存 Small の証明は不変。
F2 の IsKappaSmall は `Cardinal.mk K.N < μ` の定義だけなので、P は Core の同型の不等式を
定義展開で使える。F2 からの import、他レーンの証明のコピー、新しい小ささ述語は導入しない。
任意の Hull が μ-small とは主張せず、既存 canonical hull とその同じ包含・因子化を保持する。

公開名（namespace `SerrePositivity.InfinityCategories.SmallSubcomplex`）：

- `hasCardinalLT_innerHornData`・`hasCardinalLT_innerHornStep`・`hasCardinalLT_innerHornStage`
  (`Core/InnerHornClosureCardinal`)：同じ充填試験族・一段・各段の濃度評価。
- `hasCardinalLT_innerHornClosure`・`cardinal_innerHornClosure_lt`（同じ葉）：
  宇宙多相な HasCardinalLT と、同じ宇宙での `Cardinal.mk (innerHornClosure A).toSSet.N < μ`。
- `hasCardinalLT_model`・`hasCardinalLT_hull_obj` (`Core/SmallHullCardinal`)：
  既存 model と既存 canonical hull の対象の μ-small 性。
- `hullOfCardinalBound`・`hasCardinalLT_hullOfCardinalBound_obj`・`exists_hull_hasCardinalLT`
  （同じ葉）：濃度から宇宙的 Small を放電し、既存 Hull の構造全体と μ-small 性を得る。

補助葉 `Core/SimplicialCardinalBounds` は非退化単体から各次数への評価と、その可算和による逆向きを供給する。
HasCardinalLT は mathlib の宇宙多相な既存述語。既存 F2 の定義を複製しない。
公開型の直接適用例は F2 の定義だけを読み、閉包・全段・model・Hull の既存 IsKappaSmall を検査した。
本体の import 閉包には F2・KST・EInfinity・straightening はない。

検証：SmallHullCardinal 対象ビルド 1409 jobs、同じ宇宙の IsKappaSmall に対する
閉包・各段・model・Hull の直接適用、宇宙を分けた閉包・model・Hull の直接適用、
18宣言の公理・禁止依存・ModelCategory／強極限仮定監査、Core/F1/F1B 三監査が全て通過。
許容公理は標準三つのみ。既存の深層三ファイルは不変、監査登録は Core 末尾への追記のみ。

## (8) 保存済み供給

完了コミット `871293866`。F1/Coherent/RepresentableHomInfinity の
`representableHomCoherentIso` が元の豊穣 Hom の全実現と指定共変 Hom の全図式 FunctorIso。
同じ恒等点回収は `representableHomCosliceIdentity_value`。8葉120宣言・F1 全監査通過。
x 方向の追加自然性は未公開。詳細・三段目・検証記録は同コミットの本計画・本文を参照。
(8) の葉に限る、既存上流4入口経由の KST.Spectra 推移 import 例外は保持する。
今回の (9)/(9b) には拡大しない。R が整理する4経路も同コミットに記録済み。

## (9)・(9b) 三段目と公開界面

1. [x] foundations §6・§8、Ind-S 進捗、両要求型を確認する。
2. [ ] (9) の短辺・合成端・全長 Hom を保持する制御二胞体族を構成する。
3. [ ] encode ≫ longHom = 𝟙 と零単体の全 native Hom 回収を示し、
   同じ三面の充填空間の可縮性と既存充填との比較を供給する。
4. [x] (9b) の三面を固定する実三単体族を構成し、末尾の全 native Hom の HEq も保持する。
5. [ ] 自分の対象と F1 監査だけを通し、git commit --only と実施記録を保存して報告・停止する。

要求正本：(9) は kst-lanes/L3-fibration.md の indS9ControlledTriangleFamilyRequest、
(9b) は kst-lanes/archive/L3-controlled-factorization-tetra-proposal.md の
controlledFactorizationTetraFamilyRequest。仕様型の緩和・存在仮定化はしない。

現在地：FixedInnerHornFamily・TetrahedronFamilyFilling・FactorizationTetrahedronFaces・
TetrahedronPathFold・InnerHornFamilyPrescribedVertices の対象ビルド通過。
TetrahedronLongHomReplacement・StrictFaceHomConstancy も対象ビルド通過。
TetrahedronFoldedLongHom・TetrahedronStrictCompositionHom と全族復元を接続済み。
F1 全監査と新規11葉93宣言の公理・禁止依存・ModelCategory 監査が通過。
controlledFactorizationTetraFamily は K-B 正本の要求型への直接適用も通過。
(9b) の末尾 HEq は二つの長い辺の一致より強く、全 native Hom 写像の一致を要求する。
δ₁F と δ₂F の native Hom は、Path(0,3) への異なる面包含で制限されるため、
辺の単体恒等式だけで HEq を結論しない。元の要求型を保持して明示制御を調べる。

(9b) 公開：`controlledFactorizationTetraFamily`、入口
`F1/Diagrams/ControlledFactorizationTetrahedronFamily`。全 K の三面厳密回収と
要求どおりの full native Hom HEq を含む。内部合成値の定値性を指定厳密面から導き、
長い Hom を論理和で畳み込み、零骨格の選択を同じ全ホーンへ延長する。
(9) は未完了。(9) 追加全対角仕様（ユーザー採用）も保持し、標準区間比較の
像条件との整合性を検査中。KST の仕様ファイルは読取りのみ。
