# Ind-S 供給計画 v3

## 引き継ぎ（2026-10-26、(9b) 完了・(9) 正規化条項採用後に続行）

- 所有：F1/・F1B/・Core/ の新規葉と三監査の末尾追記、本計画。
- 深層編集は禁止、F2 は読み取り専用、K-B・Sp・EInfinity は import しない。
  F1 の straightening は使用可。(8) の限定推移 import 例外は今回へ拡大しない。
- 今回：(9) 制御二胞体族と (9b) 因子分解三単体族。提供先は K-B。
- 現在地：(9b) 完了 77a33b4c9。像条件 f18c411f3、正規化補助 69b3436ab、
  長 Hom からの実二胞体全族 218e5b449。逆向き longHom 実射も対象ビルド通過。
- 主要補助宣言：tetrahedronFamilyExtensionSpace_compare・factorizationTetrahedronFamily_faces・
  innerHornFamily_lift_with_vertices。いずれも両主仕様全体の供給完了とは扱わない。
- 依存と提供：Core/F1/mathlib の既存界面を読み取り専用で使用。連絡・提案はユーザー経由。
- 保存済み：正規化など6葉 69b3436ab、85宣言・F1全監査通過。
- 保存済み追加7葉：全族制御・小さい native Hom 回収、23宣言・F1全監査通過。
- 今回保存対象：TriangleNativeCompositeValue・ControlledTriangleNativeReadout・
  ControlledTriangleFamilySpaces・ControlledTriangleReadoutMap、KanIntervalEvaluation の補助名重複修正。
- 既知の問題：(9) の encode・longHom の存在と厳密切断は未供給。(9b) は全 HEq 込みで完了。
- 残り：下記三段目 2〜5。見積りは制御全族の有限座標を確認した後に更新する。
- 次の一手：対角制限の既存 API の import 入口を確定し、単射 encode と厳密切断、
  正規化後の全対角式と元の t との固定ホーン内の可逆比較を接続する。
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

現在地：(9b) の有限 native Hom 制御と全族復元を接続済み。
F1 全監査と新規11葉93宣言の公理・禁止依存・ModelCategory 監査が通過。
controlledFactorizationTetraFamily は K-B 正本の要求型への直接適用も通過。
(9b) の末尾 HEq は二つの長い辺の一致より強く、全 native Hom 写像の一致を要求する。
δ₁F と δ₂F の native Hom は、Path(0,3) への異なる面包含で制限されるため、
辺の単体恒等式だけで HEq を結論しない。元の要求型を保持して明示制御を調べる。

(9b) 公開：`controlledFactorizationTetraFamily`、入口
`F1/Diagrams/ControlledFactorizationTetrahedronFamily`。全 K の三面厳密回収と
要求どおりの full native Hom HEq を含む。内部合成値の定値性を指定厳密面から導き、
長い Hom を論理和で畳み込み、零骨格の選択を同じ全ホーンへ延長する。
(9) は未完了。追加全対角仕様は下記の採用済み正規化へ修正。KST の仕様は読取りのみ。

## (9) 追加全対角条項：像障害と設計変更案

追加条項はユーザー採用済み（提案ファイルの未採用という見出しより最新指示を優先）。
対象は全 t : T₀。Lt の直接 path 評価を r : K → H とすると、δ₁Tt 全体が
標準 coherentHomIntervalComparison の像に厳密に入ることを要求する。
これは readout の定義を選べば自動的に成立する条件ではない。

検証した有限座標（新規 F1/Diagrams/ の二葉）：
- CanonicalIntervalTriangle.rightMappingSpacePrism_target_triangle：右 prism の
  終点側三角形は σ₁ ≫ δ₁。そのため標準像の終点側三角形は必ず σ₁ の像。
- WholeDiagonalImageObstruction.coherentIntervalFamily_target_triangle_degenerate：
  任意の raw Hom の全一単体族にも同じ退化条件が必要。
- factorizationTrianglePrism_diagonal_not_canonical_of_distinct_edges：
  一番面の長辺と第一辺が異なる三単体を明示三角柱へ引くと、長辺族は標準像に入らない。
- factorizationTrianglePrism_boundary_of_unit_faces：同じ三角柱の二短辺は、
  零番面・三番面が単位合成なら、元の恒等と元の辺への定値族を厳密に回収する。

数学的な反例の形（主仕様の否定の閉じた Lean 項としては未登録）：
X は点、Z は二対象間に唯一の同型を持つ groupoid の nerve（可縮 Kan）。
異なる二点の射 u₀,u₁ : X → Z は異なるがホモトピック。
s を二短辺 u₀,id_Z、長辺 u₁ の coherent 二単体とする。
Λ[3,2] の三面を (u₀,id_Z) の厳密合成、s、(id_X,u₀) の厳密合成にして充填 F を取る。
三角柱の頂点を (0,0)↦0,(0,1)↦1,(1,0)↦1,(1,1)↦1,(2,0)↦2,(2,1)↦3
に送って F を引く。二短辺は上の定値族だが、長辺の終点側三角形は s。
その第一辺 u₀ と長辺 u₁ は異なるので σ₁ の像にはなく、新条項の標準像条件を満たさない。
上の二葉はこの像条件・三角柱座標・非像判定を証明する。具体的 Z と s の実装は未登録。

採用済み修正（ユーザー回答、2026-10-26）：旧 (9) の全条件と (9b) を保持し、
追加条項の Tt を normalize(t) := encode(longHom(t)) の二胞体に置く。
射として normalize = longHom ≫ encode。既存の切断式から冪等性と読出し保存を得る。
元の t と normalize(t) の比較は同じ固定ホーン空間 T 内の可逆比較として別に保持する。
元の全 t の長辺との厳密等号は主張しない。ユーザー採用により承認待ちなく実施を続行。
追加2葉23宣言の公理・禁止依存・ModelCategory 監査と F1 全監査が通過。残件は旧 (9) の厳密切断・各 k の full native Hom 回収、正規化後の全対角式と可逆比較。

## (9) 採用後の構成補助・現在地

- 69b3436ab：正規化の冪等性・読出し保存・同じ固定 fiber 内の VertexIso、
  単射 encode からの頂点指定左逆、有限 native Hom 置換、合成端固定 L の可縮性。
  対象6葉・85宣言・F1全監査通過。その後、重複した evaluateFunctorAt_pre を新設葉から除き、
  既存 PreFiberKan の正本を import する形に修正。補助6葉は84宣言で再監査通過。
- 218e5b449：controlledTriangleFamily_exists_of_longHom
  （ControlledTriangleLongHomFamily）。合成端固定 q から元の全ホーンを厳密に持つ F を作り、
  各 k の全 native Hom の関手頂点を HEq で回収。追加7葉23宣言・F1全監査通過。
- 今回：controlledTriangleReadoutMap_exists（ControlledTriangleReadoutMap）。
  要求正本の実 T → L と全 t,k の full native Hom 回収。単なる直接 path の値ではない。
  任意の二胞体の合成端を固定短辺から依存和で同定し、零骨格指定持ち上げを二度使う。
  正本から切り出した読出し要求型への直接適用が通過。実 encode・固定 fiber の VertexIso、
  controlledTriangleSplit_of_mono_encoder による単射 encoder への切断還元を追加。 対象8葉61宣言・F1全監査通過（読出し27、encoder等13、対角輸送1、path座標20）。 入口は ControlledTriangleReadoutMap・ControlledTriangleEncoderMap・ ControlledTriangleSplitReduction・ControlledCompositionDiagonalTransport・TriangleLabelPathCoordinates。 encode の単射性・厳密切断は未供給で、(9) 全体の完了とは扱わない。

ユーザー許可（2026-10-26）：(9) 新規葉に限り、既存の
F1/MappingSpaces/CompositionCorrespondenceDiagonalPullback から
F1/KanModels/KanEquivalenceLiftingFibration 経由の推移 F2/CatInfinity import を許可。
確認済み閉包は本体952モジュール中 F2/CatInfinity が22、KST・EInfinity は0。
その他の F2、F2 の直接 import は禁止。例外は新規監査項に明記する。
R が第 I 段終了時に当該 F1/KanModels → F2/CatInfinity 依存を Core へ降ろす。
深層・F2 は読み取り専用。残件は単射 encode・厳密切断。正規化後の全対角式は下記の実 encoder で供給済み。

次の三段目：三対象ラベルの二切断座標 → 対角上の全区間を保つ Kan 延長 →
二短辺・native Hom・標準全対角を保つ全次数の encoder → 単射性 → 厳密左逆。
単なる可縮性から encode の単射性や厳密切断は結論しない。

追加8葉62宣言・F1全監査通過：TriangleDiagonalKanExtension、TriangleTwoCutCoordinates、 TriangleSeparatedLongHom / DirectHom、TriangleLabelHomReplacement、TriangleLabelBaseline 等。 全対角の Hom 座標の厳密回収まで。全次数の encoder への接続・単射性・厳密左逆は未完了。

追加16葉80宣言・F1全監査通過：triangleSeparatedSimplex、triangleSeparatedSimplex_naturality、 triangleSeparatedFamily と同じ全 K・L 上の二短辺の厳密回収を公開。単射性・厳密切断は未完了。

追加16葉61宣言・F1全監査通過：実 controlledTriangleCoherentEncoder、controlledTriangleCoherentEncoder_native、 controlledTriangleCoherentNormalization_diagonal、controlledTriangleCoherentNormalization_vertexIso。 入口 ControlledTriangleCoherentEncoderNative。元の全ホーン・各 k の full native Hom・正規化後の全 K 対角・同じ固定 fiber 内の VertexIso を実構成。 K-B 正本から厳密切断だけを True に置換した型への直接適用も通過（標準三公理のみ）。 厳密切断は依然未供給で、(9) 完了とは扱わない。

実 encoder の16葉61宣言は e6ec74eb9 で保存。追加 ControlledTriangleNormalizedRequest（13宣言・対象ビルド・葉監査・F1全監査通過）は採用済み正本の厳密切断も保持し、 controlledTriangleNormalizedRequest_of_mono で実 encoder の単射性一つへ還元する。単射性は未供給入力。
