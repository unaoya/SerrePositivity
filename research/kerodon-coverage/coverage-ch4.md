# Kerodon 第 4 章（The Homotopy Theory of ∞-Categories）の被覆状況

調べた日：2026-11-06（main 7d5006ee7、Mathlib は .lake/packages/mathlib）。Kerodon 本文は 64 個の Subsection ページを curl で取得した（ch4pages/、主張の一覧は envs.txt）。

- 判定は内容で行った（宣言名・主張で grep）。引用の有無は判定に使っていない。
- sorry について：`SerrePositivity/InfinityCategories/` の中で `sorry` を含むのは `ModelBridge/Inputs/KanQuillen.lean:42`（Hovey 3.6.5、Kan–Quillen モデルの存在）だけ。層の順序（Simplicial → Core → Kan → Coherent → F1/F1B …）から、下の表に挙げた Core・F1・F1B の宣言はこのファイルを import しない。表の宣言はすべて sorry なし。Mathlib にも sorry はない。
- 下の表のファイルは、断りがなければ `SerrePositivity/InfinityCategories/` からの相対パス。ML: は Mathlib（`Mathlib/AlgebraicTopology/...` など）。

## 表

| 番号 | 見出し | 判定 | 出どころ | 主な宣言・ファイル | 注記 |
|---|---|---|---|---|---|
| 4.1.1 | Inner Fibrations of Simplicial Sets | あり | Mathlib + 自前 | ML `SSet.InnerFibration`、`quasicategory_of_innerFibration`（Quasicategory/InnerFibration）；`innerFibration_vertexFiber_quasicategory`（Core/InnerFiber）、`quasicategory_pullback_of_innerFibration_right`（Core/InnerPullback） | 神経の上での判定（Prop 4.1.1.10）は見つからない |
| 4.1.2 | Subcategories of ∞-Categories | 一部 | 自前 | `fullSubcomplexOnVertices_quasicategory`（Core/FullSubcomplexFibration） | 充満部分圏（Def 4.1.2.15–17）だけ。一般の部分圏（Def 4.1.2.2）と hC の部分圏との対応（Prop 4.1.2.10）はない |
| 4.1.3 | Inner Anodyne Morphisms | あり | Mathlib | ML `innerAnodyneExtensions`、`innerAnodyneExtensions_eq_llp_rlp`、`HasSmallObjectArgument innerHornInclusions`（AnodyneExtensions/Inner/Basic） | 分解（Prop 4.1.3.2）は small object argument から得られる |
| 4.1.4 | Exponentiation for Inner Fibrations | あり | Mathlib + 自前 | ML `innerFibration_pullbackObjObjπ`（= Prop 4.1.4.1）、`Quasicategory ((ihom A).obj X)`（Inner/PushoutProduct）；`trivialKanFibration_pre_of_innerAnodyne`（Core/InnerAnodyneEquivalence、≈ 4.1.4.4） | |
| 4.1.5 | Inner Covering Maps | なし | — | — | |
| 4.2.1 | Left and Right Fibrations of Simplicial Sets | あり | 自前 | `LeftFibration`・`RightFibration`・`leftFibration_innerFibration`（Core/RightFibration）、`vertexFiber_kanComplex_of_leftFibration`（Core/LeftFiberKan） | |
| 4.2.2 | Fibrations in Groupoids | なし | — | — | 通常の圏の fibration in groupoids はない（Kan ⇔ hX が亜群、は 4.4.2 の行に記載） |
| 4.2.3 | Left and Right Covering Maps | なし | — | — | |
| 4.2.4 | Left Anodyne and Right Anodyne Morphisms | あり | 自前 | `leftAnodyneExtensions`・`leftAnodyneExtensions_horn`（Core/JoinCells）、`stdSimplex_firstVertex_leftAnodyne`（Core/InitialBoundaryTransport、= Cor 4.2.4.11） | 定義は rlp.llp（Kerodon は飽和クラス）。両者は同値 |
| 4.2.5 | Exponentiation for Left and Right Fibrations | あり | 自前 | `leftFibration_pullbackObjObjπ`・`leftAnodyneExtensions_pushoutObjObj_right`（F1/Fibrations/LeftAnodynePushoutProduct、= 4.2.5.1・4.2.5.3）、`ihom_map_leftFibration`（F1/Fibrations/LeftFibrationInternalHom） | 右側は F1B/Fibrations/RightAnodyneTensor |
| 4.2.6 | The Homotopy Extension Lifting Property | 一部 | 自前 | `trivialKanFibration_relativeHom_of_leftAnodyne`（F1/Fibrations/LeftAnodynePushoutProduct） | 「left fibration ⇒ ev₀ が trivial Kan fibration」は 4.2.5 の一般形から出る。逆向き（Prop 4.2.6.1）と Cor 4.2.6.2 は述べられていない |
| 4.3.1 | Slices of Categories | あり | Mathlib | ML `CategoryTheory.Over`/`Under`、`Limits.Cone` | 通常の圏の話。Mathlib の標準構成で足りる |
| 4.3.2 | Joins of Categories | あり | Mathlib | ML `CategoryTheory.Join`（CategoryTheory/Join/Basic・Opposites・Sum） | N(C⋆D) ≅ N(C)⋆N(D) は見つからない |
| 4.3.3 | Joins of Simplicial Sets | あり | 自前 | `join`・`joinStdSimplexIso`（Core/Join）、`join_quasicategory`（F1/Joins/JoinQuasicategory、= Cor 4.3.3.25） | inner fibration の join（Prop 4.3.3.24）の一般形は見つからない |
| 4.3.4 | Joins of Topological Spaces | なし | — | — | |
| 4.3.5 | Slices of Simplicial Sets | あり | 自前 | `sliceOver`・`sliceOverCurry`/`Uncurry`（Core/Slice、= Prop 4.3.5.13）、`sliceUnder`（Core/Coslice） | |
| 4.3.6 | Slices of ∞-Categories | あり | 自前 | `sliceOverProjection_rightFibration`・`sliceOver_quasicategory`（Core/RightFibration、= Joyal 4.3.6.1）、`joinUnion_innerAnodyne_of_rightAnodyne`（Core/JoinAnodyne、= 4.3.6.4）、`sliceUnderRestrict_leftFibration`（Core/FibrationRestriction、= 4.3.6.14） | |
| 4.3.7 | Slices of Left and Right Fibrations | あり | 自前 | `relativeCosliceMap_leftFibration`（Core/RelativeCoslice）、Core/ConeAnodyne（= Lemma 4.3.7.8）、`rightFibration_pullback_snd`（Core/RightFibrationContractible） | |
| 4.4.1 | Isofibrations of ∞-Categories | 一部 | 自前 | `equivalenceLifting_iff_inner_and_invertibleTargetLifting`（F1B/Fibrations/IsofibrationCriterion）、`InvertibleTargetLifting` | 「inner + 同型の持ち上げ」（Def 4.4.1.4）は使える形である。ただし isofibration という名の定義はない。通常の圏の isofibration（Def 4.4.1.1）と双対（4.4.1.8）もない |
| 4.4.2 | Isomorphisms and Lifting Properties | あり | 自前 | `kanComplex_iff_isGroupoid`（Core/KanCharacterization、= 4.4.2.1）、`isInvertibleEdge_iff_hasFinalHornFillers`（Core/OuterHornConverse、= Joyal 4.4.2.6）、`innerFibration_lift_finalHorn`（Core/RelativeOuterHorn、≈ 4.4.2.13）、`rightFibration_trivialKanFibration_of_contractible_fibers`（Core/RightFibrationContractible、= 4.4.2.14） | conservative（Def 4.4.2.7）の一般の定義はない |
| 4.4.3 | The Core of an ∞-Category | あり | 自前 | `quasicategoryCore`・`quasicategoryCoreLift`（F1/Categories/QuasicategoryCore）、`quasicategoryCore_kanComplex`（F1/Categories/CoreKan、= 4.4.3.11）、`coreMap_fibration_of_kanEquivalenceLifting`（F1B/CatInfinity/CoreIsofibration、≈ 4.4.3.7） | |
| 4.4.4 | Natural Isomorphisms | あり | 自前 | `FunctorIso`（Core/Equivalence）、`functorIsoOfPointwiseInvertibleHomotopy`（Core/FunctorEdgePointwise、= Thm 4.4.4.4） | |
| 4.4.5 | Exponentiation for Isofibrations | 一部 | 自前 | `EquivalenceLifting.internalHom`（F1B/Fibrations/EquivalenceLifting）、`trivialKanFibration_equivalencePathEndpoint_zero`（Core/EquivalencePathLifting、≈ Cor 4.4.5.5、Isom(C)＝`equivalencePath`） | 相対版（Prop 4.4.5.1・4.4.5.8）は見つからない |
| 4.5.1 | Equivalences of ∞-Categories | あり | 自前 | `QCatEquivalence`・`IsQCatEquivalence`（Core/Equivalence）、`IsQCatEquivalence.comp` ほか（Core/EquivalenceCalculus）、`isQCatEquivalence_of_trivialKanFibration`（Core/TrivialFibrationEquivalence） | 圏 hQCat そのもの（Constr 4.5.1.1）は作っていない |
| 4.5.2 | Minimal ∞-Categories | なし | — | — | |
| 4.5.3 | Categorical Pullback Squares | 一部 | 自前 | `equivalencePath`（= Isom(C)）、`equivalencePathReplacement`・`…Projection_trivialKanFibration`（Core/EquivalencePathReplacement、≈ Cor 4.5.3.24 の分解） | 「categorical pullback square」の定義と、その対称性・推移性・ホモトピー不変性（4.5.3.8–22）はない。KST/Comparison/HomotopyPullback の `IsHomotopyPullback` は Kan 複体の場合 |
| 4.5.4 | Categorical Equivalence | あり | 自前 | `IsPrecompositionEquivalence`（Core/PrecompositionEquivalence、Prop 4.5.4.8 の形の定義）、`isPrecompositionEquivalence_of_innerAnodyne`（= Cor 4.5.4.14） | 定義は Kerodon の Def 4.5.4.1 ではなく、同値な 4.5.4.8 の条件を採っている |
| 4.5.5 | Categorical Pushout Squares | 一部 | 自前 | `isPrecompositionEquivalence_of_pushout_gluing`（Core/PrecompositionPushoutGluing）、`isPullback_pre_of_isPushout` | 個別の貼り合わせ補題だけで、categorical pushout という名の定義はない |
| 4.5.6 | Isofibrations of Simplicial Sets | あり | 自前 | `EquivalenceLifting`（F1B/Fibrations/EquivalenceLifting、= Def 4.5.6.5）、`equivalenceLifting_iff_inner_and_invertibleTargetLifting`（= Prop 4.5.6.1）、`EquivalenceLifting.internalHom`（≈ 4.5.6.15） | 名前は isofibration ではなく `EquivalenceLifting` |
| 4.5.7 | Isofibrant Diagrams | なし | — | — | |
| 4.5.8 | Relative Exponentiation | なし | — | — | ML `ExponentiableMorphism` は LCCC の意味で、Kerodon の exponentiable（4.5.8.10）とは別物 |
| 4.6.1 | Morphism Spaces | 一部 | 自前 | `pinchedHom_kanComplex`（Core/MappingSpaceRightKan、≈ 4.6.1.10）、`IsQCatEquivalence.isFullyFaithful`（Core/EquivalenceFullyFaithful、≈ 4.6.1.14）、`pinchedHomMap_rightFibration`（Core/MappingSpaceFibration、≈ 4.6.1.21） | 方針として写像空間は右 pinched で定義している。pinched でない Hom_C(X,Y)（Constr 4.6.1.1）は作っていない |
| 4.6.2 | Digression: Universal Property of the Join | あり | 自前 | `fatJoin`（= blunt join ⋄、Core/FatJoin）、`isPrecompositionEquivalence_fatJoinComparison`（Core/FatJoinGeneralComparison、= Thm 4.6.2.8） | 引用が最も多い（447 件） |
| 4.6.3 | Digression: Categorical Mapping Cylinders | 一部 | 自前 | `equivalenceInterval`（= N(codiscrete Bool)）・`relativeEquivalenceCylinder`（Core/EquivalenceCylinder・RelativeEquivalenceCylinder）、`exists_equivalenceCylinder_extension_of_functorIso`／`nonempty_functorIso_of_equivalenceCylinder_extension`（Core/EquivalenceCylinderFunctorIso） | 可逆な区間による円柱という具体例だけ（Prop 4.6.3.1 相当）。一般の定義（Def 4.6.3.3）と Thm 4.6.3.8 はない |
| 4.6.4 | Oriented Fiber Products | 一部 | 自前 | `laxSlice`（Core/LaxSlice）、`isQCatEquivalence_sliceLaxMap`（Core/SliceLaxEquivalence、= Thm 4.6.4.19 の slice 側）、`cosliceLaxMap`（Core/CosliceLaxEquivalence） | 一般の oriented fiber product C ×→_E D（Def 4.6.4.1）はない。slice の場合を fat join で表した模型だけ |
| 4.6.5 | Pinched Morphism Spaces | あり | 自前 | `PinchedHom.Simplex`（PinchedHom/Basic）、`pinchedHom_kanComplex`（= 4.6.5.5）、`pinchedHomToSliceFiber`（Core/PinchedSlice）、`pinchedHomPiZeroEquiv`（Core/MappingSpacePiZero） | 4.6.1 の Hom がないため、pinch inclusion が同値であること（Prop 4.6.5.10）はない |
| 4.6.6 | Digression: Diagrams in Slice ∞-Categories | 一部 | 自前 | `isQCatEquivalence_sliceConeFamilyMap`（Core/SliceConeFamilyEquivalence、= Lemma 4.6.6.7・Ex 4.6.6.8）、`coneFamily`（Core/ConeFamily）、`isQCatEquivalence_fatJoinComparison_fixedDiagram` | 両側 slice C_{f₋/ /f₊} の一般形（Thm 4.6.6.5）は見つからない（K₋ = ∅ の場合はある） |
| 4.6.7 | Morphism Spaces in the Homotopy Coherent Nerve | あり | 自前 | `coherentHomComparison_isSimplicialHomotopyEquivalence`（F1/Coherent/HomEquivalence、= Thm 4.6.7.5）、`coherentNerveMap_isFullyFaithful_iff`（F1/Coherent/NerveFullyFaithful）、Φ の模型（F1/Coherent/ResolutionFlags、= 4.6.7.23・Ex 4.6.7.27） | DoldKanComparison/ にも多数（引用 603 件） |
| 4.6.8 | Composition of Morphisms | 一部 | 自前 | `pinchedHomCompositionHomotopy`（Derived/PinchedHomCompositionHomotopy、dg nerve の場合 ≈ Prop 4.6.8.21）、`kanMappingComposition`（Kan/KanMappingComposition、辺の合成） | 一般の ∞ 圏での Hom(X,Y)×Hom(Y,Z)→Hom(X,Z)、単位律・結合律（4.6.8.11–12）、豊穣ホモトピー圏（4.6.8.13）はない |
| 4.7.1 | Truncated Objects | なし | — | — | |
| 4.7.2 | Truncated Morphisms | なし | — | — | |
| 4.7.3 | Initial and Final Objects | あり | 自前 | `IsTerminalVertex`・`isTerminalVertex_iff_trivialKanFibration`（Core/Terminal、= Cor 4.7.3.12）、`isTerminalVertex_iff_pinchedHom_isContractibleKan`（Core/TerminalMappingSpace、= Def 4.7.3.1 との同値）、`IsTerminalVertex.of_vertexIso`（Core/TerminalTransport）・Core/TerminalUniqueness | 定義は境界充填（= Prop 4.7.3.11） |
| 4.7.4 | Discrete and Subterminal Objects | なし | — | — | F1/Fibrations/SubterminalFiber の subterminal は単体的集合 B の性質で、対象の性質ではない |
| 4.7.5 | Monomorphisms | なし | — | — | |
| 4.7.6 | Locally Truncated ∞-Categories | なし | — | — | ML Coskeletal.lean は神経の 2-余骨格性だけ |
| 4.7.7 | n-Categories | なし | — | — | ML `StrictSegal`（神経の特徴づけ）は n = 1 に近い話にとどまる |
| 4.7.8 | Minimality Conditions | なし | — | — | |
| 4.7.9 | Higher Homotopy Categories | なし | — | — | h₁ = hC（第 1 章）だけがある |
| 4.8.1 | Essentially Surjective Functors | あり | 自前 | `IsEssentiallySurjective`・`isEssentiallySurjective_iff_hoFunctor`（Core/FullyFaithful） | 本質的像（Def 4.8.1.11）は名前の付いた定義としてはない |
| 4.8.2 | Full Functors | なし | — | — | full・n-full はない |
| 4.8.3 | Faithful Functors | 一部 | 自前 | `IsFullyFaithful`（Core/FullyFaithful、= Def 4.8.3.1）、`IsFullyFaithful.preimageVertexIso`、`isFullyFaithful_of_trivialKanFibration`（Core/MappingSpaceTrivialFibration） | fully faithful だけ。faithful・n-faithful（Def 4.8.3.8・4.8.3.12）はない |
| 4.8.4 | Detecting Equivalences of ∞-Categories | あり | 自前 | `isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`（Core/EquivalenceFullyFaithful、= Thm 4.8.4.1）、`qCatEquivalenceOfFullyFaithfulEssentiallySurjective`（Core/FullyFaithfulEquivalence）、Core/FullyFaithfulBaseChange・FullyFaithfulFibration | Thm 4.8.4.6（Fun(Δ¹,−)^≃ による判定）と DK 同値（Cor 4.8.4.9）は、F1/Coherent/NerveFullyFaithful に近いものがある |
| 4.8.5 | Categorically Connective Functors | なし | — | — | |
| 4.8.6 | Digression: n-Categorical Fibrations | なし | — | — | |
| 4.8.7 | Canonical Factorizations | なし | — | — | |
| 4.8.8 | Categorically Connective Morphisms of Simplicial Sets | なし | — | — | |
| 4.9.1 | Ordinals and Well-Orderings | あり | Mathlib | ML `Ordinal`、`Ordinal.cof`、`WellOrderingRel.isWellOrder`（整列可能定理） | |
| 4.9.2 | Cardinals and Cardinality | あり | Mathlib | ML `Cardinal`、`Cardinal.cantor`、SetTheory/Cardinal/SchroederBernstein | |
| 4.9.3 | Small Sets | あり | Mathlib | ML `Cardinal.IsRegular`、`Cardinal.IsInaccessible`、`IsStrongLimit`、`HasCardinalLT` | 指数的共終数 ecf（Def 4.9.3.16）はない |
| 4.9.4 | Small Simplicial Sets | あり | 自前 | `IsKappaSmall`（Core/FilteredExchange/SmallSimplicialShapes、= Def 4.9.4.1）、`isKappaSmall_join`（Core/FilteredExchange/SmallJoin、= Cor 4.9.4.13）、`isKappaSmall_prod`・`isKappaSmall_pushout_of_mono`（F2/Ind） | Ex^∞ と同型類の数え上げ（4.9.4.16・4.9.4.20）は見つからない |
| 4.9.5 | Essential Smallness | 一部 | 自前 | `hull`（Core/SmallQuasicategoryHull）、Core/InnerHornClosureCardinal（≈ Prop 4.9.5.7）、`HasSmallKanModel`（F1/Universe/SmallKanModel） | 宇宙を使った小さい模型という形。essentially κ-small の一般の定義（Def 4.9.5.1）はない |
| 4.9.6 | Small Kan Complexes | 一部 | 自前 | `HasSmallKanModel`（F1/Universe/SmallKanModel） | 定義だけ。ホモトピー群による判定（Prop 4.9.6.1）はない |
| 4.9.7 | Local Smallness | 一部 | 自前 | `IsLocallySmall`（F2/Presentable/LocallySmall）、`IsLocallySmall.of_fullyFaithful` | 宇宙 u+1/u の形だけ（κ 一般ではない）。Cor 4.9.7.9 はない |
| 4.9.8 | Small Fibrations | 一部 | 自前 | `HasEssentiallySmallFibers`（F1/Universe/SmallKanModel、left fibration 用） | 定義だけ。推移性（4.9.8.14・4.9.8.16）はない |

## 集計

| 節 | あり | 一部 | なし |
|---|---|---|---|
| 4.1 Inner Fibrations | 3 | 1 | 1 |
| 4.2 Left and Right Fibrations | 3 | 1 | 2 |
| 4.3 Slice and Join | 6 | 0 | 1 |
| 4.4 Isomorphisms and Isofibrations | 3 | 2 | 0 |
| 4.5 Equivalence | 3 | 2 | 3 |
| 4.6 Morphism Spaces | 3 | 5 | 0 |
| 4.7 Truncated Objects / Higher Homotopy Categories | 1 | 0 | 8 |
| 4.8 Full, Faithful, Ess. Surjective | 2 | 1 | 5 |
| 4.9 Size Conditions | 4 | 4 | 0 |
| **計（64）** | **28** | **16** | **20** |

出どころ（「あり」と「一部」の 44 件）：自前だけが 36 件、Mathlib だけが 6 件（4.1.3、4.3.1、4.3.2、4.9.1–4.9.3）、両方が 2 件（4.1.1、4.1.4）。

## 引用番号のずれ（抜き取り検査）

方法：citations.csv にある第 4 章の項目番号は 54 種類ある。そのすべてについて、今の Kerodon のページに同じ番号の項目があるかを確かめた。あわせて見出し語（Proposition など）も照合した。さらに 20 件ほどについて、Lean 側の docstring の内容と Kerodon の主張を突き合わせた。

- 存在しない番号：0 件。
- 内容が一致：4.4.2.6・4.4.2.14・4.4.2.15・4.4.3.1・4.5.1.16・4.5.3.24・4.6.2.10・4.6.4.25・4.6.6.8・4.6.7.23・4.7.3.12・4.8.3.9・4.3.6.14 など。番号はおおむね今の版に合っている。
- ずれ・要修正：
  - `Proposition 4.7.3.6`（Core/Terminal.lean:79,146、終対象の境界充填による定義）。今の 4.7.3.6 は Example（coherent nerve の終対象）。内容に合うのは Prop 4.7.3.11。
  - `§4.3.5` が join の構成に使われている（Core/Join.lean で 66 件）。join は §4.3.3、§4.3.5 は slice。古い版の番号の可能性がある。
  - `§4.5.5`（categorical pushout）が、可逆 path による引き戻しに使われている（Core/PullbackZigzag ほか、42 件の一部）。§4.5.3 のつもりの可能性がある。要確認。
  - 見出し語だけのずれ：`Proposition 4.6.4.19`（今は Theorem）、`Proposition 4.6.6.7`（今は Lemma）、`Proposition 4.6.7.16`（今は Corollary、114 件）。番号と内容は合っている。
  - `Kerodon 4.8.4.1`（KST/Spectra/KanCompositeCancellation ほか）が Kan 複体の π 同型からのホモトピー同値に使われている。4.8.4.1 は「同値 ⇔ 充満忠実かつ本質的全射」なので、Whitehead 型（第 3 章）の方が合う。
  - `Proposition 4.8.4.5` が「充満忠実な inner fibration の基底変換」に使われている（Core/FullyFaithfulBaseChange）。今の 4.8.4.5 は n-full と ∂Δⁿ の持ち上げ。近いが同じではない。
