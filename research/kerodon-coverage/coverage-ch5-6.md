# Kerodon 第 5・6 章の形式化の範囲（2026-11-06 時点、main 7d5006ee7）

調べ方：Kerodon の各 Subsection のページ（pages/5.x.y.html、6.x.y.html）から主な定義・定理を抜き出し（items.json）、
宣言名の一覧（decls.txt、SerrePositivity/ 以下の全 .lean）を内容の語で grep し、代表の宣言のファイルと型を読んだ。
引用（citations.csv）は手がかりとしてだけ使った。Mathlib は .lake/packages/mathlib を grep。

sorry：`grep -rnw 'sorry|admit'` を InfinityCategories/ 全体（F1 2965 本、F1B 1519 本、Core 631、Coherent 40、
HomotopyLimits 1184、Kan 254、F2 2308）にかけて、実の `sorry` は `ModelBridge/Inputs/KanQuillen.lean:42` の 1 件だけ
（第 5・6 章の宣言とは無関係。F1・F1B から ModelBridge の import はない）。`axiom` 宣言は 0。
下の「あり」「一部」はすべて sorry なし。

注意：`F1/Cocartesian/`（Cat∞ 値 straightening）は集約 `F1.lean` から import されない休止の集約 `F1/Cocartesian.lean`
（「休止中の Cat∞ 値構成を検証・再開するときに明示的にビルドする」）にある。sorry はないが main のビルド対象外。

凡例：あり＝主な定義と主要な定理がある／一部＝定義だけ・一部の定理だけ／なし。出どころ：自＝SerrePositivity、M＝Mathlib。
「引用」＝docstring の Kerodon 引用数（joined.md）。

## 第 5 章 Fibrations of ∞-Categories（46）

| 番号 | 見出し | 引用 | 判定 | 出どころ | 根拠（宣言・ファイル）と欠けているもの |
|---|---|---|---|---|---|
| 5.1.1 | Cartesian Edges of Simplicial Sets | 93 | あり | 自 | `IsCocartesianEdge`・`IsCartesianEdge`（Core/CocartesianEdge.lean、F1/Fibrations/CartesianEdge.lean）、`isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration`（Prop 5.1.1.14、F1/Cocartesian/Coslice*.lean）、`isCartesianEdge_of_isInvertibleEdge`（Prop 5.1.1.9） |
| 5.1.2 | Cartesian Morphisms of ∞-Categories | 10 | 一部 | 自 | Cor 5.1.2.4（三角形の二辺から、`isCocartesianEdge_triangle_*`、F1/Cocartesian/Composition.lean）あり。Prop 5.1.2.1（写像空間のホモトピー引き戻しによる判定）は名前で見当たらない |
| 5.1.3 | Locally Cartesian Edges | 21 | 一部 | 自 | locally (co)cartesian 辺の定義なし。Prop 5.1.3.11 の写像空間判定に当たる補題（`coslicePostcompFiberMap_source_equivalence_of_target`、F1/MappingSpaces/CosliceFiberPostcomposition.lean）だけ |
| 5.1.4 | Cartesian Fibrations | 60 | あり | 自 | `cartesianFibrations`・`cocartesianFibrations`（F1/Fibrations/CartesianFibration.lean）、`CocartesianHornFibration`（Core/CocartesianFibration.lean）、`leftFibration_iff_cocartesianFibration_all_edges`（Prop 5.1.4.15、F1/Fibrations/AllEdges.lean）、`cocartesianFibration_comp`・`cocartesianFibration_pullback_snd`。Prop 5.1.4.9（isofibration）はなし |
| 5.1.5 | Locally Cartesian Fibrations | 0 | なし | — | 定義（Def 5.1.5.1）も Cor 5.1.5.11 もない |
| 5.1.6 | Fiberwise Equivalence | 38 | 一部 | 自 | Thm 5.1.6.1 は Δ¹ 上（`isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts`、F1/Cocartesian/CrossingComparison.lean）と left fibration の一般の底（`isQCatEquivalence_of_leftFibration_fibers`、F1/Fibrations/LeftFibrationFiberComparison.lean）だけ。cocartesian の一般の底はない |
| 5.1.7 | Equivalence of Inner Fibrations | 0 | なし | — | Def 5.1.7.1 以下なし（Core/RelativeMappingCylinder.lean の相対写像柱は別物） |
| 5.2.1 | Exponentiation for Cartesian Fibrations | 0 | 一部 | 自 | left fibration の内部 Hom だけ（`ihom_map_leftFibration`、F1/Fibrations/LeftFibrationInternalHom.lean）。Thm 5.2.1.1 の (co)cartesian 版はない |
| 5.2.2 | Covariant Transport Functors | 123 | あり | 自 | `IsEdgeTransport`・`IsCocartesianTransport`（Def 5.2.2.4、F1/Transport/EdgeTransport.lean）、`transportChoiceSpace_isContractibleKan`（Prop 5.2.2.8、F1/Transport/Choices.lean）。Thm 5.2.2.20 は未確認 |
| 5.2.3 | Example: The Relative Join | 105 | あり | 自 | `joinDiagonal`（Construction 5.2.3.1、F1/Joins/JoinDiagonal.lean）、`relativeJoin_quasicategory`（Prop 5.2.3.11）、`cocartesianFibration_interval_of_lift`（Prop 5.2.3.15） |
| 5.2.4 | Fibrations over the 1-Simplex | 443 | あり | 自 | Thm 5.2.4.1（F1/Cocartesian/CrossingComparison.lean、F1/Joins/RelativeJoinCocartesianFibration.lean）、Prop 5.2.4.5（`prismEndpoint_one_rightAnodyne` ほか、F1/Diagrams/）。Cor 5.2.4.2・5.2.4.4 は未確認 |
| 5.2.5 | The Homotopy Transport Representation | 64 | あり | 自 | `homotopyTransport`・`homotopyTransport_unique`（Construction 5.2.5.2、F1/Transport/HomotopyTransport.lean）、`IsEdgeTransport.comp`（Prop 5.2.5.1） |
| 5.2.6 | Elements of Set-Valued Functors | 0 | 一部 | M | `CategoryTheory.Functor.Elements`（Mathlib/CategoryTheory/Elements.lean、Construction 5.2.6.1）。Prop 5.2.6.8（nerve と left covering の対応）はない |
| 5.2.7 | Covering Space Theory | 0 | 一部 | M | `IsCoveringMap`・持ち上げ・monodromy（Mathlib/Topology/Covering/、Topology/Homotopy/Lifting.lean）。Thm 5.2.7.1 の分類と単体集合の left covering map はない |
| 5.2.8 | Parametrized Covariant Transport | 4 | 一部 | 自 | Def 5.2.8.1（`parametrizedFiberTransport`、`fiberTransportFamily`、F1/Transport/ParametrizedFiberTransport.lean）。Prop 5.2.8.4〜Construction 5.2.8.9（enriched homotopy transport）はない |
| 5.3.1 | The Strict Transport Representation | 191 | あり | 自 | Construction 5.3.1.5（`nerveUnderMap`・`relativeFunctor*`、Core/NerveUnderMap.lean）、`cocartesianStrictTransportEvaluate_isQCatEquivalence`（値と fiber の同値、F1B/Fibrations/CocartesianStrictTransportEquivalence.lean） |
| 5.3.2 | Homotopy Colimits of Simplicial Sets | 78 | 一部 | 自 | Construction 5.3.2.1（`simplicialReplacement*`、F1/Diagrams/SimplicialReplacement.lean）、Remark 5.3.2.12（`simplicialReplacementAssembly`）。Prop 5.3.2.17・Cor 5.3.2.21（ホモトピー不変性・関手）は見当たらない |
| 5.3.3 | The Weighted Nerve | 223 | あり | 自 | Def 5.3.3.1（F1/Weighted/Nerve.lean）、`weightedNerveProjection_cocartesianFibration`（F1/Weighted/NerveCocartesianFibration.lean） |
| 5.3.4 | Scaffolds of Cocartesian Fibrations | 79 | あり | 自 | `CocartesianScaffold`（Def 5.3.4.2）、`cocartesianUniversalScaffold_isCocartesianScaffold`（Prop 5.3.4.8、F1B/CocartesianScaffold/Definition.lean）、`tautScaffold_isCocartesianScaffold`（5.3.4.11・5.3.4.17） |
| 5.3.5 | Application: Classification of Cocartesian Fibrations | 194 | あり | 自 | `cocartesianUniversalScaffold_isPrecompositionEquivalence`（Thm 5.3.5.7・5.3.5.6、F1B/CocartesianScaffold/Comparison.lean）、`weightedNerveCocartesianTransportUnit_isQCatEquivalence`（F1/Weighted/NerveCocartesianUnit.lean）。底は通常の圏の nerve（原典どおり）。Thm 5.3.5.6 の「局所化した関手圏の同型類との全単射」という形の明示はない |
| 5.3.6 | Application: Relative Exponentials | 31 | 一部 | 自 | Lemma 5.3.6.6（`cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`）、`markedCocartesianFunctorSpace`。Prop 5.3.6.7・5.3.6.10 は未確認 |
| 5.3.7 | Application: Path Fibrations | 33 | 一部 | 自 | Cor 5.3.7.5（`cocartesianHornFibration_coneRestriction`、Core/ConeRestrictionCocartesianFibration.lean）。Thm 5.3.7.8（oriented fiber product の射影）は名前で見当たらない |
| 5.3.8 | Digression: Minimal Fibrations | 0 | なし | — | — |
| 5.4.1〜5.4.9 | ∞-Bicategories（9 小節：Definitions、Interior Fibrations、Slices、Local Thinness、Pith、Four-out-of-Five、Functors、Strict ∞-Bicategories、Comparison of hTr） | 0 | なし（9） | — | ∞-bicategory は意図して導入しない（F1/README.md「§5.4 … 新たな基盤として導入する経路は採らず」）。Mathlib の `SSet.QCat.strictBicategory` は h₂QCat（6.2 で使う）で ∞-bicategory ではない |
| 5.5.1 | Digression: Slicing and the Homotopy Coherent Nerve | 0 | なし | — | Thm 5.5.1.21 の slice 比較は避け、fiber の比較を別に証明する方針（F1/README.md） |
| 5.5.2 | The ∞-Category of Pointed Spaces | 34 | あり | 自 | `PointedSpaceInfinity`・`pointedSpaceProjection_leftFibration`（Construction 5.5.2.1・Prop 5.5.2.2、F1/Categories/PointedSpaces.lean）、`pointedSpaceFiberVertexEquiv`。Prop 5.5.2.8（coslice comparison）は見当たらない |
| 5.5.3 | The ∞-Category of ∞-Categories | 28 | あり | 自 | `CatInfinity`・`catInfinity_quasicategory`（Construction 5.5.3.1・Prop 5.5.3.3、F1/Categories/CatInfinity.lean）、`quasicategoryCore_kanComplex`（F1/Categories/CoreKan.lean）。Prop 5.5.3.15 以下（truncation・単射）はない |
| 5.5.4 | The ∞-Bicategory of ∞-Categories | 0 | なし | — | — |
| 5.5.5 | ∞-Categories with a Distinguished Object | 0 | なし | — | QC_*・QC_Obj → QC（Prop 5.5.5.11 の普遍 cocartesian fibration）がない |
| 5.6.1 | Elements of Category-Valued Functors | 0 | 一部 | M | Def 5.6.1.1・5.6.1.5（`CategoryTheory.Grothendieck`、`Pseudofunctor.Grothendieck`/`CoGrothendieck`）、反変版の fibered 性（Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean、Prop 5.6.1.3 の双対）。Prop 5.6.1.16・Cor 5.6.1.17（分類）はない |
| 5.6.2 | Elements of QC-Valued Functors | 121 | 一部 | 自 | 𝒮 値だけ：`leftUnstraightening F := pullback pointedSpaceProjection F`（Example 5.6.2.9、F1/StraighteningLeft/LeftUnstraightening.lean）。QC 値の ∫（Def 5.6.2.1・Prop 5.6.2.2）は QC_Obj がないのでない |
| 5.6.3 | Comparison with the Category of Elements | 0 | なし | — | — |
| 5.6.4 | Comparison with the Weighted Nerve | 0 | 一部 | 自 | Kan 値だけ：`exists_kanWeightedUnstraighteningUnit`（F1/Diagrams/KanWeightedUnstraighteningUnit.lean）。Prop 5.6.4.8（QCat 値）はない |
| 5.6.5 | The Universality Theorem | 88 | 一部 | 自 | 𝒮 値：`leftStraighteningInfinityMap_isQCatEquivalence`（qcat 底で LFib(B) ≃ Fun(B,𝒮) の ∞ 圏同値、F1/StraighteningLeft/LeftStraighteningInfinityEquivalence.lean）、`exists_coherentUnstraighteningRepresentation_extension`（Thm 5.6.5.12 の left 版、F1/Coherent/RepresentationExtension.lean）。QC 値（Thm 5.6.0.2）は通常の圏の nerve 上の構成 `cocartesianStraighteningCoherentMap` の同値が Δⁿ だけ（`cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`、F1/Cocartesian/FiniteSimplexEquivalence.lean） |
| 5.6.6 | Application: Corepresentable Functors | 0 | あり | 自 | `covariantRepresentableInfinity`（F1/Yoneda/CovariantRepresentableInfinity.lean）、`covariantCosliceClassificationIso`（Thm 5.6.6.13 相当、F1/Yoneda/CovariantCosliceClassification.lean）、`IsCorepresentableSmallSpaceFunctor`（F2/Presentable/CorepresentabilityEquivalence.lean）。引用 0 だが内容はある |
| 5.6.7 | Application: Extending Cocartesian Fibrations | 0 | なし | — | Prop 5.6.7.2、Cor 5.6.7.5（isofibration）・5.6.7.6（exponentiable）なし |
| 5.6.8 | Transport Witnesses | 95 | 一部 | 自 | left fibration 版：`transportWitnessSpace`、`smallTransportWitnessSpace_isContractibleKan`（Thm 5.6.8.3 の left 版、F1/Universe/SmallWitnessContractible.lean）、`transportRepresentationInnerExtension_isContractibleKan`（Lemma 5.6.8.10）。cocartesian 版はない |
| 5.6.9 | Proof of the Universality Theorem | 43 | 一部 | 自 | left 版の証明の部品（`pointWitnessIntervalBoundary_trivialKanFibration` ほか、F1/Transport/PointWitness*.lean）。Lemma 5.6.9.1（Δ¹ 上 cocartesian の TW 制限）の cocartesian 版はない |

## 第 6 章 Adjoint Functors（19）

| 番号 | 見出し | 引用 | 判定 | 出どころ | 根拠と欠けているもの |
|---|---|---|---|---|---|
| 6.1.1 | Adjunctions | 2 | あり | M | `Bicategory.Adjunction`（Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean）。自前は `QCatAdjunction`（abbrev） |
| 6.1.2 | Adjuncts | 1 | あり | M＋自 | `homEquiv₁`・`homEquiv₂`・`mateEquiv`（Mathlib/…/Adjunction/Mate.lean）、`QCatAdjunction.homEquiv`（F1B/Adjunction/Adjunction.lean） |
| 6.1.3 | Uniqueness of Adjoints | 4 | あり | M＋自 | `conjugateIsoEquiv`（Mate.lean）、圏では `Adjunction.leftAdjointUniq`。自前 `rightAdjointIso`・`leftAdjointIso` |
| 6.1.4 | Adjoints of Isomorphisms | 0 | 一部 | M | `adjointifyCounit`・`Equivalence.mkOfAdjointifyCounit`（Cor 6.1.4.2 相当）。Prop 6.1.4.1・6.1.4.6〜7 は名前で見当たらない |
| 6.1.5 | Composition of Adjunctions | 1 | あり | M＋自 | `Bicategory.Adjunction.comp`、自前 `QCatAdjunction.comp` |
| 6.1.6 | Duality in Monoidal Categories | 0 | 一部 | M | `ExactPairing`・`tensorLeftAdjunction`（Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean）。一対象双圏の随伴との同一視はない |
| 6.2.1 | Adjunctions of ∞-Categories | 79 | あり | 自（土台 M） | `QCatAdjunction`・`mkOfHomTriangles`（Def 6.2.1.1、Mathlib の `SSet.QCat.strictBicategory` 上）、`intervalMap_isSimplicialHomotopyEquivalence`（Prop 6.2.1.17、F1B/Adjunction/AdjunctionMappingSpaces.lean） |
| 6.2.2 | Reflective Subcategories | 3 | あり | 自 | `ReflectiveSubcategory`（F1B/Localization/Reflective.lean）、`counitIso`・`idempotentIso`（Cor 6.2.2.26 の方向、ReflectiveIdempotence.lean）、`isLocal_iff_essentialImage` |
| 6.2.3 | Local Objects | 0 | 一部 | 自 | `IsLocalObject W`（Def 6.2.3.1、HomotopyLimits/Presentable/LocalObjects.lean）と局所同値の補題群。Cor 6.2.3.15（localizing な集まり ↔ 反射的部分圏の全単射）は見当たらない |
| 6.2.4 | Stability Properties of Reflective Subcategories | 0 | なし | — | (co)cartesian fibration に沿う安定性なし |
| 6.2.5 | Correspondences | 0 | なし | — | Prop 6.2.5.4（Δ¹ 上の bicartesian fibration ↔ 随伴）なし |
| 6.2.6 | Local Existence Criterion | 16 | あり | 自 | `unitCommaInitialCondition_iff`（F1B/Adjunction/UniversalUnitComma.lean）、`qcat_exists_adjunction_unitHom_iff`（Cor 6.2.6.5、QCatUnitHomCriterion.lean）、`exists_leftAdjoint_iff_covariantHom_representable`（Prop 6.2.6.1 相当、F2/Presentable/AdjunctionFromHomRepresentation.lean） |
| 6.2.7 | Digression: ∞-Categories with Short Morphisms | 0 | なし | — | — |
| 6.3.1 | Localizations of ∞-Categories | 4 | あり | 自 | `IsLocalization`・`invertingFunctors`（Def 6.3.1.9・Prop 6.3.1.13、F1B/Localization/Localization.lean）、`IsLocalization.saturate`（Saturation.lean）、`IsLocalization.exists_extension` |
| 6.3.2 | Existence of Localizations | 0 | なし | — | Prop 6.3.2.1（任意の (C, W) の局所化の存在）なし。F1B/Localization/DwyerKan/（約 600 本、hammock 型の構成）は途中で、入口 DwyerKan.lean は空の骨組み・集約未登録 |
| 6.3.3 | Reflective Localizations | 4 | あり | 自 | `ReflectiveSubcategory.isLocalization`（反射は局所化、ReflectiveLocalization.lean）、`QCatAdjunction.isLocalization`（可逆な余単位、AdjointLocalization.lean）。Def 6.3.3.4 を名前つきで定義してはいない |
| 6.3.4 | Fiberwise Localization | 0 | なし | — | — |
| 6.3.5 | Universal Localizations | 0 | なし | — | — |
| 6.3.6 | Subdivision and Localization | 0 | 一部 | M | Mathlib の `sd`・`ex`（SimplicialSet/Subdivision.lean）と `SSet.Nonsingular`（Def 6.3.6.6）だけ。Thm 6.3.6.1 などの局所化の主張はない |

## 集計

| 章 | あり | 一部 | なし | 計 |
|---|---|---|---|---|
| 5 | 13 | 16 | 17 | 46 |
| 6 | 9 | 4 | 6 | 19 |

出どころ別（あり・一部）：第 5 章は自前 26・Mathlib 3（5.2.6、5.2.7、5.6.1）。第 6 章は 6.1 の 6 小節が Mathlib（うち 3 は自前の QCat 版もある）、6.2・6.3 は 6.3.6 の Mathlib を除き自前。

節別：5.1 は 2/3/2（あり/一部/なし）、5.2 は 4/4/0、5.3 は 4/3/1、5.4 は 0/0/9、5.5 は 2/0/3、5.6 は 1/6/2。
6.1 は 4/2/0、6.2 は 3/1/3、6.3 は 2/1/3。

## straightening（5.5〜5.6）の到達点

- **𝒮 値（left fibration）**：一般の底でできている。`leftStraighteningInfinityMap B : LeftFibrationInfinity B ⟶ SpaceInfinityFunctor (ulift B)` は任意の単体集合 B で定義され、本質的全射性 `leftStraighteningInfinityMap_isEssentiallySurjective` も任意の B。充満忠実性と ∞ 圏同値 `leftStraighteningInfinityMap_isQCatEquivalence` は `[Quasicategory B]` のとき。これは Cor 5.6.0.6（同型類の全単射）より強い関手 ∞ 圏の同値（原典の Remark 5.6.0.5 の予告に当たる）。right fibration・前層版は `RightStraighteningInfinityEquivalence`。原典は C を任意の単体集合とするので、qcat でない底での単射側だけが明示されていない。
- **Cat∞ 値（cocartesian）**：休止。構成 `cocartesianStraighteningCoherentMap C` は通常の圏 C の nerve 上だけ。同値は Δ⁰・Δ¹・Δ²・一般の Δⁿ（`cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`）と subsingleton の場合まで。一般の底（Thm 5.6.0.2）、QC_Obj → QC と QC 値 ∫（5.5.5・5.6.2）、5.6.3・5.6.4（QCat 値）、5.6.7 はない。これらは休止の集約 F1/Cocartesian.lean にあり、main の F1.lean からは import されない。計画の再開点は infinity-core-F1.md「第 II 段の再開点」（有限セル・骨格降下 24〜48 時間など）。
- 通常の圏の上の分類（5.3.5、Cat 値の strict 化経由）は cocartesian でもできている。

## 番号のずれ（抜き取り）

ページから取った現行の項目一覧と、引用の「種類＋番号」をすべて照合した（第 5・6 章の item 形 2,758 件）。存在しない番号は 0 件、種類の食い違いは 11 件だけ。番号はおおむね現行版どおり。内容の抜き取り（12 件の無作為抽出と、多い番号の確認）では次のとおり：

1. **5.6.0.6（984 件）**：現行版でも Corollary 5.6.0.6＝𝒮 値の分類（left fibration ↔ C → 𝒮、任意の単体集合 C）で、番号は正しい。件数が多いのは「使われ方」の決まり文句として補助補題に広く付いているため（例：HomotopyLimits/SectionsFiberwiseEquivalence.lean の切断比較）。
2. **Remark 5.6.2.5（93 件）**：内容がずれている。現行の 5.6.2.5 は「通常の圏上の strictly unital な F : C → Cat の nerve と ∫ の比較（§5.6.3 の予告）」。引用している `vertexFiberPullbackIso`（Core/VertexFiberPullback.lean）・`fiberComparisonBaseChange`・`leftUnstraighteningTransformationFamily_restriction` は「∫F の fiber」の話で、現行では **Example 5.6.2.19（Fibers of the ∞-Category of Elements）** と Example 5.6.2.9 に当たる。古い版の番号の可能性が高い。
3. **5.3.7.5（9 件）**：「Proposition」と書かれているが、現行は Corollary 5.3.7.5（内容は合っている）。
4. **5.2.3.18（2 件）**：「Corollary」と書かれているが、現行は Example 5.2.3.18（内容は合っている）。
5. **Proposition 5.2.4.5（335 件）**：現行の「錐の比較図式（式 5.24）」と合っている。件数は prism・cone の補助補題に広く付いているため。
6. **Theorem 5.3.5.7（165 件）**：現行の「cocartesian かつ scaffold ⇔ 圏同値」と合っている。`scaffoldFiniteCollapse_zero_obj` のような途中の部品にも付いている。
7. **Corollary 5.6.5.15（34 件）**：現行は「covariant transport 表現は一意（同型）」。引用先は `simplexPrismFirstVertex_leftAnodyne` などの証明の部品（証明が使う Δ¹ × E の議論）で、ずれではない。
8. 5.2.2.8、5.1.3.11、5.6.8.10、6.2.1.17、6.2.6.5、6.3.1.13 は内容も現行と合っている。
9. 節だけの引用「Kerodon 5.6」（42 件、`coherentMaximalPathFunctor` など）は小節を指していない。

一般的な注意：引用数は「その定理そのものの形式化」の数ではない。大半は補助補題の「使われ方」の記載。逆に 5.6.6 のように引用 0 でも内容があるものがある。
