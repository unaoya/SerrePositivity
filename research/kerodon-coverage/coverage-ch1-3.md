# Kerodon 第 1・2・3 章の形式化カバー状況（2026-11-06）

対象：SerrePositivity（主に InfinityCategories/、KST/Spectra・KST/ProExcision、HomotopicalAlgebra/、DifferentialGraded/）と Mathlib（.lake/packages/mathlib）。
判定は Kerodon 現行版（https://kerodon.net/tag/<Tag> を 11-06 に取得、pages/ に保存）の各 Subsection の主な定義・定理と、宣言名・主張の grep による照合。証明の中身は読んでいない（公理監査も未実行）。

- 判定：あり＝主な定義と主要な定理が sorry なしである／一部＝定義だけ、または一部の定理だけ／なし。
- 出どころ：SP＝自前（SerrePositivity）、ML＝Mathlib。
- パスは SP なら `SerrePositivity/` から、ML なら `Mathlib/` からの相対パス。IC＝`SerrePositivity/InfinityCategories`。
- sorry：`grep -rlw sorry` の結果、InfinityCategories・KST・HomotopicalAlgebra・DifferentialGraded で実際の sorry があるのは `IC/ModelBridge/Inputs/KanQuillen.lean`（Hovey 3.6.5 の Kan–Quillen モデルの存在、文献の引用入力）の 1 件だけ。もう 1 件の該当（F2/Presentable/Localization/All.lean）は docstring 中の文字列。KanQuillen は ModelBridge/Inputs 以外からは import されていない。下の表の宣言はこれに依存しない。

## 第 1 章 The Language of ∞-Categories

| 番号 | 見出し | 判定 | 出どころ | 主な宣言・ファイル | 注記 |
|---|---|---|---|---|---|
| 1.1.1 | Face Operators | あり | ML | `SimplexCategory.δ`, `SimplicialObject.δ_comp_δ`（SimplicialObject/Basic）, `SemiSimplexCategory` | 1.1.1.9（面作用素による半単体対象の記述）は半単体圏の定義でまかなえる |
| 1.1.2 | Degeneracy Operators | あり | ML | `SSet.degenerate`/`nonDegenerate`, `exists_nonDegenerate`・`unique_nonDegenerate_*`（SimplicialSet/Degenerate）, SimplexCategory/GeneratorsRelations | Eilenberg–Zilber 補題（1.1.2.10）と生成元・関係による表示 |
| 1.1.3 | Dimensions of Simplicial Sets | あり | ML | `SSet.HasDimensionLT`（Dimension）, `hasDimensionLT_prod`（FiniteProd, 1.1.3.6）, `X.S`/`X.N`（単体の圏） | 1.1.3.11 の同値をすべて満たすかは未確認 |
| 1.1.4 | The Skeletal Filtration | あり | ML | `SSet.skeleton`, `skeletonOfMono`（相対セル複体, 1.1.4.12）（Skeleton）, `boundary`・`Boundary.hom_ext` | `sk n ≅ skeleton (n+1)` は Mathlib の TODO |
| 1.1.5 | Discrete Simplicial Sets | 一部 | SP | `vertexDiscrete`（IC/Core/VertexDiscrete.lean） | 頂点の定数単体的集合だけ。ev₀ の随伴（1.1.5.1・1.1.5.8）と判定 1.1.5.14 はない |
| 1.1.6 | Directed Graphs as Simplicial Sets | 一部 | ML | `OneTruncation₂`, `oneTruncation₂`（SimplicialSet/HomotopyCat） | 次元 ≤1 の単体的集合と有向グラフの圏同値（1.1.6.9）はない |
| 1.2.1 | Connected Components of Simplicial Sets | 一部 | ML | `SSet.π₀`, `mapπ₀`, `IsConnected`（SimplicialSet/PiZero） | 連結成分の直和への分解（1.2.1.13）と π₀ の有限積保存（1.2.1.27）はない（Mathlib の TODO） |
| 1.2.2 | The Singular Simplicial Set | あり | ML | `TopCat.toSSet`（SingularSet） | 構成だけの節 |
| 1.2.3 | Geometric Realization | 一部 | ML | `SSet.toTop`, `sSetTopAdj`（SingularSet）, TopAdj | 随伴（1.2.3.4–1.2.3.5）はある。π₀(S) ≅ π₀\|S\|（1.2.3.19）と 1.2.3.10 はない |
| 1.2.4 | Horns | あり | ML（＋SP） | `SSet.horn`（Horn）, HornColimits; `hornReverseIso`（IC/Core/Opposite.lean） | |
| 1.2.5 | Kan Complexes | 一部 | ML＋SP | `SSet.KanComplex`（KanComplex）, `prod_kanComplex`（IC/Kan/HomotopyProduct.lean）, IC/Kan/HomotopyZeroRelations.lean（1.2.5.10） | Sing が Kan であること（1.2.5.8、Mathlib の TODO）と単体群が Kan であること（1.2.5.9）はない |
| 1.3.1 | The Nerve of a Category | あり | ML | `CategoryTheory.nerve`, `nerveFunctor`（SimplicialSet/Nerve） | |
| 1.3.2 | Example: Monoids | なし | — | （`nerve (SingleObj M)` で代用できる） | Mon → Set_Δ の充満忠実性（1.3.2.7）はない |
| 1.3.3 | Recovering a Category from its Nerve | あり | ML | `nerveFunctor.full`/`nerveFunctor.faithful`（SimplicialSet/NerveAdjunction） | |
| 1.3.4 | Characterization of Nerves | 一部 | ML | `StrictSegal`, `Nerve.strictSegal`（SimplicialSet/StrictSegal）, Quasicategory/StrictSegal | nerve ⇒ 一意充填の向きだけ。逆向き（1.3.4.1 の ⇐）は Mathlib の TODO |
| 1.3.5 | The Nerve of a Groupoid | あり | SP | `groupoidNerve_kanComplex`（IC/Stable/CoreFlag/GroupNerveHomotopy.lean）, `kanComplex_iff_isGroupoid`（IC/Core/KanCharacterization.lean） | 1.3.5.2 の両向き（hoFunctor ∘ nerve と併せて） |
| 1.3.6 | Homotopy Category of a Simplicial Set | あり | ML | `SSet.hoFunctor`, `nerveAdjunction`（HomotopyCat, NerveAdjunction） | |
| 1.3.7 | Path Category of a Directed Graph | 一部 | ML | `CategoryTheory.Paths`（自由圏）。`hoFunctor` の定義に使われている | 1.3.7.5 と自由圏の特徴付け 1.3.7.11 はない |
| 1.4.1 | Objects and Morphisms | あり | ML | `SSet.Quasicategory`（Quasicategory/Basic）, `SSet.Edge`（CompStruct） | 定義の節 |
| 1.4.2 | The Opposite of an ∞-Category | あり | ML＋SP | `SSet.opFunctor`（SimplicialSet/Op）, `quasicategory_op`（IC/Core/Opposite.lean, 1.4.2.6） | |
| 1.4.3 | Homotopies of Morphisms | あり | ML | `HomotopicL`/`HomotopicR` の同値関係性と一致（Quasicategory/TwoTruncated） | |
| 1.4.4 | Composition of Morphisms | あり | ML | `Quasicategory₂`, `HomotopyCategory₂` の合成（Quasicategory/TwoTruncated） | |
| 1.4.5 | Homotopy Category of an ∞-Category | あり | ML＋SP | `HomotopyCategory₂`; `homotopyCategoryBridge`（IC/Core/HomotopyCategoryBridge.lean）, `bridge_naturality`（HomotopyCategoryMap, 1.4.5.7） | |
| 1.4.6 | Isomorphisms | あり | SP | `IsInvertibleEdge`（IC/Core/InvertibleEdge.lean）, `kanComplex_iff_isGroupoid`（1.4.6.10 を含む） | ML の `Edge.InvStruct` もある |
| 1.5.1 | Examples of Functors | あり | ML | `nerveFunctor`, `TopCat.toSSet`, `hoFunctor` | 番号付きの項目がない節 |
| 1.5.2 | Commutative Diagrams | 一部 | ML | 図式＝射 K ⟶ C, `SSet.CompStruct` | 定義だけ。1.5.2.6（次元 ≤1 の図式の可換性）はない |
| 1.5.3 | The ∞-Category of Functors | あり | ML | `ihom`（SSet の MonoidalClosed）, instance `Quasicategory ((ihom A).obj X)`（AnodyneExtensions/Inner/PushoutProduct, Thm 1.5.3.7） | 1.5.3.3（nerve と関手圏）は未確認 |
| 1.5.4 | Digression: Lifting Properties | あり | ML | `HasLiftingProperty`, `MorphismProperty.llp`/`rlp`, `IsStableUnderTransfiniteComposition`, `HasSmallObjectArgument` | |
| 1.5.5 | Trivial Kan Fibrations | あり | SP＋ML | `trivialKanFibrations`（IC/Core/Terminal.lean, Def 1.5.5.1）, `boundaryGenerators_leftClass`（HomotopicalAlgebra/Simplicial/Generators.lean, 1.5.5.4/1.5.5.14 相当）, `IsContractibleKan`（IC/Core/ContractibleKan.lean, 1.5.5.8） | |
| 1.5.6 | Uniqueness of Composition | 一部 | ML | `innerAnodyneExtensions_pushoutObjObjι`（AnodyneExtensions/Inner/PushoutProduct, Lemma 1.5.6.9 相当） | Joyal の判定（Thm 1.5.6.1）は見つからない |
| 1.5.7 | Universality of Path Categories | 一部 | SP＋ML | `sequentialSpine_inclusion_innerAnodyne`（IC/F2/Presentable/Supply/SequentialSpineInnerAnodyne.lean）, `StrictSegal` | Thm 1.5.7.1 はない。有限 spine の inner anodyne 性（1.5.7.7）は見つからない |

## 第 2 章 Examples of ∞-Categories

| 番号 | 見出し | 判定 | 出どころ | 主な宣言・ファイル | 注記 |
|---|---|---|---|---|---|
| 2.1.1 | Nonunital Monoidal Categories | なし | — | | Mathlib には単位付きの版しかない |
| 2.1.2 | Monoidal Categories | あり | ML | `MonoidalCategory`（Monoidal/Category）, coherence | Kerodon の定義（単位を性質として扱う）との同値（2.1.2.9 など）は形式化されていない |
| 2.1.3 | Examples of Monoidal Categories | あり | ML | `CartesianMonoidalCategory`/`monoidalOfHasFiniteProducts`, `MonoidalOpposite`（Monoidal/Opposite） | 群コサイクルの例（2.1.3.3）はない |
| 2.1.4 | Nonunital Monoidal Functors | 一部 | ML | `Functor.LaxMonoidal`/`OplaxMonoidal` の単位付きの版だけ | |
| 2.1.5 | Lax Monoidal Functors | あり | ML | `Functor.LaxMonoidal`, `LaxMonoidalFunctor`, `MonObj`（Monoidal/Functor, Mon） | |
| 2.1.6 | Monoidal Functors | あり | ML | `Functor.Monoidal`（Monoidal/Functor） | |
| 2.1.7 | Enriched Category Theory | あり | ML | `EnrichedCategory`, `ForgetEnrichment`（Enriched/） | |
| 2.2.1 | Bicategories | あり | ML | `Bicategory`（Bicategory/Basic）, 三角恒等式 | |
| 2.2.2 | Examples of Bicategories | 一部 | ML | `Span`（Bicategory/Span）, `monBicategory`（Monoidal/Bimod）, `MonoidalSingleObj`（Bicategory/SingleObj） | cospan の例は未確認 |
| 2.2.3 | Opposite and Conjugate Bicategories | 一部 | ML | `Bᵒᵖ`（Bicategory/Opposites） | 2-射を反転する conjugate は未確認 |
| 2.2.4 | Functors of Bicategories | あり | ML | `LaxFunctor`, `OplaxFunctor`, `Pseudofunctor`, `StrictPseudofunctor`（Bicategory/Functor/） | |
| 2.2.5 | The Category of Bicategories | 一部 | ML | `LaxFunctor.comp`/`id`, `OplaxFunctor.comp` | 双圏のなす圏と 2.2.5.9–10 はない |
| 2.2.6 | Isomorphisms of Bicategories | なし | — | | |
| 2.2.7 | Strictly Unital Bicategories | 一部 | ML | strictly unitary な lax 関手・pseudofunctor（Bicategory/Functor/StrictlyUnitary） | 厳密単位的な双圏と 2.2.7.7 はない。このファイルの Kerodon 引用「section 2.2.2.4（tag 008G）」は旧番号で、現行では 2.2.4 |
| 2.2.8 | Homotopy Category of a Bicategory | 一部 | ML | `Pith`（Bicategory/LocallyGroupoid, Constr 2.2.8.9） | hC（2.2.8.2）と 2-category の特徴付けはない |
| 2.3.1 | The Duskin Nerve | なし | — | | Mathlib の TODO（StrictlyUnitary.lean） |
| 2.3.2 | From Bicategories to ∞-Categories | なし | — | | |
| 2.3.3 | Thin 2-Simplices of a Duskin Nerve | なし | — | | |
| 2.3.4 | Recovering a Bicategory | なし | — | | |
| 2.3.5 | Duskin Nerve of a Strict Bicategory | なし | — | | |
| 2.4.1 | Simplicial Enrichment | 一部 | ML | `SimplicialCategory`, `sHom`（SimplicialCategory/Basic） | 定義はある。Cat_Δ の極限・余極限（2.4.1.13）はない |
| 2.4.2 | Examples of Simplicial Categories | 一部 | ML＋SP | SimplicialObject の単体的圏（SimplicialCategory/SimplicialObject）, `kanObject_simplicialCategory`（IC/F1/Categories/CatInfinity.lean） | delooping・Top・conjugate の例はない |
| 2.4.3 | The Homotopy Coherent Nerve | あり | ML（＋SP） | `SimplicialThickening`, `SimplicialNerve`（SimplicialNerve）; IC/Coherent/Path.lean | 自前の Path は Notation 2.4.3.1 と包含の向きが逆（docstring に明記） |
| 2.4.4 | Path Category of a Simplicial Set | 一部 | SP＋ML | `pathPrefix` など（IC/Coherent/Path.lean, Lemma 2.4.4.16）; `SimplicialThickening`＝Path[n] | 左随伴 Path[S]（2.4.4.3）と Thm 2.4.4.10 はない |
| 2.4.5 | From Simplicial Categories to ∞-Categories | あり | SP | `simplicialNerve_quasicategory`（IC/Coherent/Quasicategory.lean, Thm 2.4.5.1）, IC/Coherent/Cube・HollowCube（2.4.5.4–2.4.5.12） | |
| 2.4.6 | Homotopy Category of a Simplicial Category | なし | — | | |
| 2.4.7 | Example: Braid Monoids | なし | — | | Mathlib には `CoxeterSystem` だけがある |
| 2.5.1 | Generalities on Chain Complexes | あり | ML | `HomologicalComplex`, `homology`, `QuasiIso`, `HomologicalComplex.monoidalCategory`（Algebra/Homology/Monoidal） | |
| 2.5.2 | Differential Graded Categories | あり | SP | `DGCategory`（DifferentialGraded/Category/Basic.lean）, `DGFunctor`（Functor/QuasiEquivalence.lean） | |
| 2.5.3 | The Differential Graded Nerve | あり | SP | `dgNerve`（IC/DGNerve/Basic.lean）, `instQuasicategory`（IC/DGNerve/Quasicategory.lean, Thm 2.5.3.10） | |
| 2.5.4 | Homotopy Category of a DG Category | あり | SP | `HomotopyCategory`（DifferentialGraded/Category/Basic）, `equivalence`/`toH0`（IC/DGNerve/HomotopyCategory.lean, 2.5.4.10） | |
| 2.5.5 | Homology of Simplicial Sets | あり | ML | `AlternatingFaceMapComplex`, `NormalizedMooreComplex`, `SSet.homology`（SimplicialSet/Homology）, DoldKan/HomotopyEquivalence（2.5.5.11 相当） | |
| 2.5.6 | The Dold–Kan Correspondence | あり | ML | `DoldKan.N`, `DoldKan.Γ`, `DoldKan.equivalence`（DoldKan/Equivalence） | 自前の DoldKanComparison はこれを使う |
| 2.5.7 | The Shuffle Product | 一部 | SP | `shuffle`・`normalizedShuffle`・`ezHomotopy`（KST/ProExcision/ShuffleChainMap, NormalizedShuffle, EZHomotopy） | ModuleCat ℤ 値の単体対象の上。Homotopy 𝟙 ≃ AW ≫ shuffle の向きだけを確認。Thm 2.5.7.14 全体は未確認 |
| 2.5.8 | The Alexander–Whitney Construction | あり | SP | `alexanderWhitney`（KST/ProExcision/AWChainMap.lean）, `normalizedAlexanderWhitney`, `awData_assoc`（IC/DoldKanComparison/AWAssociativity.lean） | |
| 2.5.9 | Comparison with the HC Nerve | あり | SP | `coherentComparison_isQCatEquivalence`（IC/DoldKanComparison/ComparisonEquivalence.lean, Thm 2.5.9.18）, `doldKanHomSpace`（ConnectiveHom, Constr 2.5.9.2） | 入口 DoldKanComparison.lean の docstring「∞ 圏の同値の証明は残る」は古い |

## 第 3 章 Kan Complexes

| 番号 | 見出し | 判定 | 出どころ | 主な宣言・ファイル | 注記 |
|---|---|---|---|---|---|
| 3.1.1 | Kan Fibrations | あり | ML | `Fibration`＝`modelCategoryQuillen.J.rlp`（SimplicialSet/CategoryWithFibrations） | |
| 3.1.2 | Anodyne Morphisms | あり | ML（＋SP） | `anodyneExtensions`（AnodyneExtensions/Basic）, `anodyneExtensions_pushoutObjObjι`（PushoutProduct, 3.1.2.9）; prism 分解（IC/F1/Joins/RelativeJoinPrism*, Lemma 3.1.2.12） | |
| 3.1.3 | Exponentiation for Kan Fibrations | あり | ML | `fibration_pullbackObjObjπ`（Thm 3.1.3.1）, instance `KanComplex ((ihom A).obj X)`（Cor 3.1.3.4） | |
| 3.1.4 | Covering Maps | なし | — | | |
| 3.1.5 | Homotopy Category of Kan Complexes | 一部 | SP | `HomotopyClasses`（HomotopicalAlgebra/Simplicial/HomotopyClasses.lean, [X,K] の商）, KanHomotopyClasses | 圏 hKan（3.1.5.10）の明示的な定義はない |
| 3.1.6 | The ∞-Category of Spaces | あり | SP | `SpaceInfinity`, `spaceInfinity_quasicategory`, `KanObject`（IC/F1/Categories/CatInfinity.lean, Constr 3.1.6.1・Prop 3.1.6.2） | |
| 3.1.7 | Homotopy Equivalences and WHE | あり | SP | `IsWeakHomotopyEquivalence`（IC/F1B/Homotopy/WeakHomotopy.lean）, `IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence`（3.1.7.13）, `isWeakHomotopyEquivalence_iff_precompose_kan`（3.1.7.17） | 3.1.7.18（正規化鎖の擬同型）は未確認 |
| 3.1.8 | Fibrant Replacement | あり | SP＋ML | `unit_anodyne`・`terminal_rlp`（HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean）, `HasSmallObjectArgument J` | |
| 3.2.1 | Pointed Kan Complexes | あり | SP | `PointedSimplicialSet`、pointed homotopy（IC/F1/Pointed/PointedHomotopy）, IC/Kan/HomotopyInvariance.lean（3.2.1.4・3.2.1.13） | |
| 3.2.2 | Homotopy Groups of a Kan Complex | あり | SP | `KanHomotopy`（IC/Kan/HomotopyIndexing.lean）, `KanHomotopyGroup`（IC/Kan/HomotopyGroups.lean, Thm 3.2.2.10）, `KanHomotopyZero.equivPiZero` | Mathlib には `PtSimplex`・`MulStruct` の部品だけがある |
| 3.2.3 | Group Structure on π_n | あり | SP | IC/Kan/HomotopyGroups.lean, IC/Kan/Commutativity.lean（n≥2 での可換性） | |
| 3.2.4 | Contractibility | 一部 | SP | `IsContractibleKan`（IC/Core/ContractibleKan.lean）, `isWeaklyContractible_iff_isContractibleKan`（IC/F1B/Homotopy/WeakContractibleKan.lean） | π_n の消滅による判定（Thm 3.2.4.3）と 3.2.4.11・3.2.4.13 は見つからない |
| 3.2.5 | The Connecting Homomorphism | あり | SP | `BoundaryLift`, `connecting`（IC/Kan/FibrationBoundary.lean） | |
| 3.2.6 | Long Exact Sequence of a Fibration | あり | SP | `exact_connecting_fiber`, `exact_fiber_total`, `exact_total_base`（IC/Kan/FibrationExactness.lean, Thm 3.2.6.1） | |
| 3.2.7 | Whitehead's Theorem for Kan Complexes | あり | SP | `homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective`, `kanPiIsomorphism_of_homotopyEquivalence`（IC/HomotopyLimits/KanWhiteheadComparison.lean） | 基点付き版は KST/Spectra/KanEquivalenceBridge.lean |
| 3.2.8 | Closure Properties of HE | 一部 | SP | `fiberMap_piIsomorphism`（IC/Kan/FibrationComparison.lean）, `simplicialSectionsMap_homotopyEquivalence_of_fibers` | 3.2.8.1 に近い。3.2.8.3–3.2.8.4 は Kan 置換の形（IC/Stable/Filtered/FilteredWeakContractibility）で一部だけ |
| 3.3.1 | Braced Simplicial Sets | なし | — | | |
| 3.3.2 | Subdivision of a Simplex | 一部 | ML | `SimplexCategory.sd`, `SSet.ex`（SimplicialSet/Subdivision） | 同相（3.3.2.3）はない |
| 3.3.3 | Subdivision of a Simplicial Set | 一部 | ML | `SSet.sd`, `sdExAdjunction`（SimplicialSet/Subdivision） | 3.3.3.17 は Mathlib の TODO |
| 3.3.4 | The Last Vertex Map | なし | — | | KST/Spectra/LastVertex* は Bousfield–Kan の weight の話で、別物 |
| 3.3.5 | Comparison of X with Ex(X) | なし | — | | |
| 3.3.6 | The Ex^∞ Functor | なし | — | | |
| 3.3.7 | Characterizations of WHE | なし | — | | |
| 3.3.8 | Extending Kan Fibrations | なし | — | | |
| 3.4.1 | Homotopy Pullback Squares | なし | — | | 定義はない。Kan fibration のファイバーの比較（IC/Kan/FibrationComparison）だけ |
| 3.4.2 | Homotopy Pushout Squares | 一部 | SP | `localized_isIso`（HomotopicalAlgebra/Simplicial/KanLocalizedLeftProper.lean）, `actual_localized_isIso`（KanPushoutComparison.lean） | 定義はない。anodyne 局所化の形で、左固有性と pushout の比較だけ |
| 3.4.3 | Mather's Second Cube Theorem | なし | — | | |
| 3.4.4 | Mather's First Cube Theorem | なし | — | | |
| 3.4.5 | WHE of Semisimplicial Sets | なし | — | | |
| 3.4.6 | Excision | なし | — | | |
| 3.4.7 | Seifert–van Kampen | なし | — | | |
| 3.5.1 | Connectivity | なし | — | | |
| 3.5.2 | Connectivity as a Lifting Property | なし | — | | |
| 3.5.3 | Coskeletal Simplicial Sets | 一部 | ML | `SimplicialObject.IsCoskeletal`, `cosk`（SimplicialObject/Coskeletal）, nerve の 2-coskeletal 性（SimplicialSet/Coskeletal） | Kan 複体の cosk（3.5.3.23）はない |
| 3.5.4 | Weakly Coskeletal Simplicial Sets | なし | — | | |
| 3.5.5 | Higher Groupoids | なし | — | | 関連：groupoid の nerve の Kan 性と StrictSegal な Kan 複体の高次ホモトピーの消滅（IC/F1/CoreFlag/StrictSegalHomotopy.lean） |
| 3.5.6 | Higher Fundamental Groupoids | なし | — | | n=1 は hoFunctor の groupoid（KST/SConstruction/FundamentalGroupoidEquivalence）で扱われている |
| 3.5.7 | Truncated Kan Complexes | なし | — | | |
| 3.5.8 | Postnikov Tower of a Kan Complex | なし | — | | |
| 3.5.9 | Truncated Morphisms | なし | — | | |
| 3.6.1 | Finite Simplicial Sets | 一部 | ML | `SSet.Finite`（Finite）, 有限単体的集合の finitely presentable 性（Presentable） | \|X\| のコンパクト性（3.6.1.12）はない |
| 3.6.2 | Exactness of Geometric Realization | なし | — | | |
| 3.6.3 | WHE in Topology | 一部 | SP | `TopologicalHomotopy.weakHomotopyEquivalences`（HomotopicalAlgebra/Topological/WeakEquivalence.lean） | 定義だけ。CW 複体の Whitehead（3.6.3.10）はない |
| 3.6.4 | The Unit Map u: X → Sing\|X\| | なし | — | | |
| 3.6.5 | Comparison of Homotopy Categories | なし | — | | Kan–Quillen のモデル構造は IC/ModelBridge/Inputs/KanQuillen.lean の sorry（Hovey 3.6.5 の引用） |
| 3.6.6 | Serre Fibrations | なし | — | | |

## 章ごとの集計

| 章 | Subsection 数 | あり | 一部 | なし |
|---|---|---|---|---|
| 1 | 31 | 20 | 10 | 1 |
| 2 | 36 | 17 | 10 | 9 |
| 3 | 46 | 12 | 9 | 25 |
| 計 | 113 | 49 | 29 | 35 |

出どころの傾向：第 1 章と第 2 章 2.1–2.2・2.5.1/2.5.5/2.5.6 は主に Mathlib。第 2 章 2.4.5・2.5.2–2.5.4・2.5.8–2.5.9 と第 3 章 3.1.6–3.2.8 は主に自前。

## 引用番号の抜き取り検査（現行 Kerodon と照合）

ch1–3 の引用 1,448 件（joined.md）は 24 の Subsection に集中している（他の 89 Subsection には引用がない）。項目番号 20 個を本文と照合した。

- 一致：1.2.5.10, 1.4.5.4, 1.4.5.7, 1.5.5.1, 2.4.4.16, 2.4.5.1/4/8–12, 3.1.2.12, 3.1.3.3/4, 3.1.6.1, 3.1.7.6/13/17, 3.2.1.4/13, 3.2.2.4/6/10, 3.2.3.1/6/7/9, 3.2.6.1。番号と内容は現行版に合っている（旧版の番号が残っている様子はない）。
- ずれ：
  - 「Kerodon §3.5 の可縮な Kan 複体」（IC/Core/ContractibleKan.lean `IsContractibleKan`）。現行の §3.5 は Truncations and Postnikov Towers。可縮な Kan 複体は Definition 1.5.5.8（または §3.2.4）。
  - 「Construction 3.2.5.1」（IC/Kan/FibrationBoundary.lean の `BoundaryLift`・`boundary`・`connecting` など 5 件）。現行では Definition 3.2.5.1 で、連結準同型そのものは Construction 3.2.5.3。番号は内容としてほぼ合っているが、種別名が違う。
- 緩い引用：「Kerodon §3.1」でホーンと境界の pushout を指す（IC/Simplicial/HornBoundaryDecomposition.lean, HornFaceBoundary.lean）。内容としては 1.2.4 と 1.1.4.10。「§1.3.3」で薄い圏の nerve への射が頂点で決まることを指す（IC/F1/Fibrations/ThinNerveInnerFibration.lean）。Remark 3.1.6.3 は N(Kan) → 𝒮 の比較だが、𝒮 の頂点と点付き空間の対応の意味で使われている。
- Mathlib 側：Bicategory/Functor/StrictlyUnitary.lean に旧番号「section 2.2.2.4（tag 008G）」がある（現行は 2.2.4）。
