import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.CategoryTheory.Filtered.Basic
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredCosliceCofinality
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "9.1 Filtered ∞-Categories" =>
%%%
number := false
tag := "kerodon-9-1"
%%%

Kerodon の 9.1 節（[Tag 05WY](https://kerodon.net/tag/05WY)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_9_1_0_1" (lean := "CategoryTheory.IsFiltered")
Kerodon Definition 9.1.0.1（[Tag 02P9](https://kerodon.net/tag/02P9)）。対応表の状態：Mathlib にある。

仮定：通常圏 C（Kerodon と一致）。結論：IsFiltered C は非空性、二対象からの共通の行き先、平行二射を等化する後合成を要求する（原文の三条件と一致）。

:::

# 9.1.1 Filtered ∞-Categories

%%%
number := false
tag := "kerodon-9-1-1"
%%%

Kerodon [Tag 02P8](https://kerodon.net/tag/02P8)

:::definition "kerodon_9_1_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity")
Kerodon Definition 9.1.1.1（[Tag 02PB](https://kerodon.net/tag/02PB)）。対応表の状態：本体にある。

仮定：Quasicategory C（Kerodon と一致）。結論：IsFilteredInfinity は任意の有限単体集合 K からの図式について JoinCocone の存在を要求する（K▷ への延長と一致）。

:::

:::definition "kerodon_9_1_1_3"
Kerodon Variant 9.1.1.3（[Tag 02PC](https://kerodon.net/tag/02PC)）。対応表の状態：一部。

有限な全図式の同じ錐の存在を仮定するとisFilteredInfinity\_op\_of\_finiteConesは同じCopのfiltered性を返す。逆向きはこの引用だけに含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_op_of_finiteCones`

:::

:::definition "kerodon_9_1_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_aleph0_iff")
Kerodon Variant 9.1.1.4（[Tag 05X0](https://kerodon.net/tag/05X0)）。対応表の状態：本体にある。

仮定：Quasicategory C と基数 κ。原文は無限基数を指定するが型自体は任意の κ を許す（Lean が弱い）。結論：任意の κ-small K の図式から余錐への延長を要求。cofiltered は同じ述語を Cᵒᵖ に適用する（原文と一致）。

:::

:::proposition "kerodon_9_1_1_16" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_4_13")
Kerodon Proposition 9.1.1.16（[Tag 02PG](https://kerodon.net/tag/02PG)）。対応表の状態：一部。

κを正則にも限るとisKappaFiltered\_sliceUnderは同じfのcosliceのκ-filtered性を直接返す。特異な無限κは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_sliceUnder`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_sliceUnder`

:::

:::proposition "kerodon_9_1_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity")
Kerodon Proposition 9.1.1.17（[Tag 02PH](https://kerodon.net/tag/02PH)）。対応表の状態：本体にある。

仮定：Quasicategory C と IsFilteredInfinity C（Kerodon と一致）。結論：台の単体集合 C の IsWeaklyContractible（原文と一致）。

:::

:::proposition "kerodon_9_1_1_18" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_3_9, kerodon_9_1_1_16, kerodon_9_1_1_17")
Kerodon Proposition 9.1.1.18（[Tag 02PJ](https://kerodon.net/tag/02PJ)）。対応表の状態：一部。

κを正則に限ると本体のcosliceのκ-filtered性・弱可縮性・対角右余終性は同じ条件(1)から(2)(4)(5)を直接与える。Archiveの逆向きは採用しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_of_kappaFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_sliceUnder_of_kappaFiltered`

:::

:::corollary "kerodon_9_1_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_equivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_iff_of_equivalence")
Kerodon Corollary 9.1.1.19（[Tag 02PK](https://kerodon.net/tag/02PK)）。対応表の状態：本体にある。

仮定：二つの quasicategory と QCatEquivalence または IsQCatEquivalence。型は κ に無限性を要求しない（Lean が弱い）。結論：IsKappaFiltered κ C↔IsKappaFiltered κ D（原文と一致）。

:::

:::corollary "kerodon_9_1_1_20"
Kerodon Corollary 9.1.1.20（[Tag 02PL](https://kerodon.net/tag/02PL)）。対応表の状態：なし。

原文と一致するiffの候補はArchiveにあり対象外。本体のfiltered⇒弱可縮だけではKanの可縮性を返す型と同じiffをここで確認できていない。

宣言：`SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_isContractibleKan`

:::

# 9.1.2 Local Characterization of Filtered ∞-Categories

%%%
number := false
tag := "kerodon-9-1-2"
%%%

Kerodon [Tag 02PM](https://kerodon.net/tag/02PM)

:::definition "kerodon_9_1_2_1"
Kerodon Definition 9.1.2.1（[Tag 02PN](https://kerodon.net/tag/02PN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：本体の filtered 性は準圏への有限図式に余錐を課す。有限図式の零ホモトピーも全体 C を標的とする。h Kan 豊穣圏で各 Hom 内の境界写像をある射で後合成して零ホモトピーにする述語は見つからない。

:::

:::theorem "kerodon_9_1_2_5"
Kerodon Theorem 9.1.2.5（[Tag 02PS](https://kerodon.net/tag/02PS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全有限図式の余錐から C 内の定値図式へのホモトピーを得る型はある。hC の豊穣 Hom での後合成による消去と比較する iff は見つからない。

:::

:::corollary "kerodon_9_1_2_6"
Kerodon Corollary 9.1.2.6（[Tag 02PT](https://kerodon.net/tag/02PT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏に頂点が存在することと、通常圏での IsFiltered の定義を確認した。hC に対して頂点の非空性に加え二対象・平行射の条件をまとめた型は見つからない。

:::

:::corollary "kerodon_9_1_2_8"
Kerodon Corollary 9.1.2.8（[Tag 02PV](https://kerodon.net/tag/02PV)）。対応表の状態：一部。

Cをcardinal-filtered前順序の圏、κ=ℵ0に限るとisKappaFiltered\_nerve\_of\_cardinalFilteredが同じnerveのfiltered性を直接返す。任意通常圏と逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered`

:::

:::corollary "kerodon_9_1_2_9"
Kerodon Corollary 9.1.2.9（[Tag 02PX](https://kerodon.net/tag/02PX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の順序集合の nerve に κ-filtered 性を移す一方向はある。局所 Kan 豊穣圏の coherent nerve と h Kan 豊穣側の条件との iff は見つからない。

:::

:::lemma_ "kerodon_9_1_2_11"
Kerodon Lemma 9.1.2.11（[Tag 02PZ](https://kerodon.net/tag/02PZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ-small 図式の余錐と有限図式を C 内で収縮する型はある。固定 Hom(X,Y) への任意の κ-small 図式を Y→Z の後合成で Hom(X,Z) 内で収縮する型は見つからない。

:::

:::lemma_ "kerodon_9_1_2_12"
Kerodon Lemma 9.1.2.12（[Tag 02Q0](https://kerodon.net/tag/02Q0)）。対応表の状態：一部。

IsFilteredInfinity.cocone\_nonemptyを有限な同じ境界∂Δnの図式に適用すると右側の全延長条件を直接得る。逆向きは引用に含まない。

宣言：`CategoryTheory.IsFiltered.cocone_nonempty`

:::

:::lemma_ "kerodon_9_1_2_14"
Kerodon Lemma 9.1.2.14（[Tag 02Q2](https://kerodon.net/tag/02Q2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全有限形状の余錐は定値面を持つ境界も含む。指定次元で一面が定値な境界の余錐存在だけから一般の境界に移す型は見つからない。

:::

# 9.1.3 Fibrations over Filtered ∞-Categories

%%%
number := false
tag := "kerodon-9-1-3"
%%%

Kerodon [Tag 02Q4](https://kerodon.net/tag/02Q4)

:::lemma_ "kerodon_9_1_3_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_1_1")
Kerodon Lemma 9.1.3.1（[Tag 05X6](https://kerodon.net/tag/05X6)）。対応表の状態：一部。

Uをleft fibrationにも強めるとtransport\_to\_cocone\_fiberはκ-filtered性が供給する同じfUの余錐から、同じfの定値底ファイバーへの自然変換を直接返す。有限版だけでなくこの一般形状の型を使う。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.leftFibration_finite_fiber_detection`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.leftFibration_transport_to_cocone_fiber`

:::

:::theorem "kerodon_9_1_3_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_6_1, kerodon_3_3_6_7, kerodon_3_3_6_9, kerodon_3_6_1_9, kerodon_6_3_6_2, kerodon_7_2_1_11, kerodon_9_1_1_17, kerodon_9_1_3_1")
Kerodon Theorem 9.1.3.2（[Tag 02Q5](https://kerodon.net/tag/02Q5)）。対応表の状態：一部。

全空間EがfilteredならisWeaklyContractible\_of\_isFilteredInfinityは同じEの弱可縮性を直接返す。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`

:::

:::corollary "kerodon_9_1_3_3"
Kerodon Corollary 9.1.3.3（[Tag 05X7](https://kerodon.net/tag/05X7)）。対応表の状態：なし。

固定宇宙の標準unstraighteningと余極限の比較は、原文の指定κ値輸送表現と任意Uの同じ全空間の比較を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit`、`SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit_isWeakHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`

:::

:::corollary "kerodon_9_1_3_4"
Kerodon Corollary 9.1.3.4（[Tag 05X8](https://kerodon.net/tag/05X8)）。対応表の状態：一部。

同じFの標準category of elementsがfilteredならその弱可縮性とcoherentDiagramTotalUnitの弱同値から、coherentDiagramTotalCoconeの同じ余極限が可縮となる。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit`、`SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit_isWeakHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`

:::

:::lemma_ "kerodon_9_1_3_5" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_4_15, kerodon_4_9_4_16")
Kerodon Lemma 9.1.3.5（[Tag 05X9](https://kerodon.net/tag/05X9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単射の像の κ-small 性はある。任意の小さい K→X の像を含み、なお弱可縮で小さい部分複体 Y を構成する型は見つからない。

:::

:::definition "kerodon_9_1_3_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_9_1_1_17, kerodon_9_1_3_1, kerodon_9_1_3_2, kerodon_9_1_3_5")
Kerodon Variant 9.1.3.6（[Tag 05XA](https://kerodon.net/tag/05XA)）。対応表の状態：一部。

無限κのκ-filtered性をfilteredへ忘れ、その同じEの弱可縮性を返す二つの型を合成して左⇒右を直接得る。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`

:::

:::proposition "kerodon_9_1_3_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_4_2, kerodon_5_1_4_1, kerodon_9_1_3_1")
Kerodon Proposition 9.1.3.8（[Tag 05XC](https://kerodon.net/tag/05XC)）。対応表の状態：一部。

IsKappaFiltered.cocone\_nonemptyを同じファイバー図式のEへの合成に適用し、coconeNullHomotopyで元の図式から同じ頂点の定値図式への自然変換を得る。(1)⇒(2)を直接満たし、全三条件の同値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered`、`SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeNullHomotopy`

:::

:::corollary "kerodon_9_1_3_11" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Corollary 9.1.3.11（[Tag 05XF](https://kerodon.net/tag/05XF)）。対応表の状態：なし。

通常圏のGrothendieck全体のfiltered性は、nerveのcocartesian射・各ファイバーの∞filtered性との比較が引用にない。通常圏の結論だけを同じ∞圏の特殊形と数えない。

宣言：`CategoryTheory.instIsFilteredGrothendieckOfαCategoryObjCat`

:::

:::corollary "kerodon_9_1_3_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_9_1_3_8")
Kerodon Corollary 9.1.3.12（[Tag 06CG](https://kerodon.net/tag/06CG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Grothendieck 構成は各ファイバーの filtered 性を仮定する。原文の全空間ごとの filtered 性と底の I 個の射の共通因子条件で同じ底上の積を扱う型は見つからない。

:::

:::corollary "kerodon_9_1_3_14" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_9_1_3_12")
Kerodon Corollary 9.1.3.14（[Tag 06CH](https://kerodon.net/tag/06CH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Grothendieck 構成では各ファイバーの filtered 性を課す。準圏の二 coslice 射影の引き戻しには弱可縮性の補題がある。任意の二 cocartesian fibration で両全空間と底の filtered 性から引き戻しの filtered 性を得る型は見つからない。

:::

# 9.1.4 Cofinal Functors of Filtered ∞-Categories

%%%
number := false
tag := "kerodon-9-1-4"
%%%

Kerodon [Tag 06CJ](https://kerodon.net/tag/06CJ)

:::definition "kerodon_9_1_4_1" (lean := "SSet.Edge")
Kerodon Definition 9.1.4.1（[Tag 06CK](https://kerodon.net/tag/06CK)）。対応表の状態：本体にある。

同じFについて∀d, ∃c, Nonempty (D.Edge d (F.app \_ c))と量化すれば、原文の弱右余終性の定義全体をそのまま表す。SSet.Edgeは指定両端の1単体であり専用述語名は不要。

:::

:::theorem "kerodon_9_1_4_5" (uses := "kerodon_1_4_0_1, kerodon_7_2_3_1, kerodon_9_1_1_16, kerodon_9_1_3_8, kerodon_9_1_4_19")
Kerodon Theorem 9.1.4.5（[Tag 06CP](https://kerodon.net/tag/06CP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では対象からの射と平行な二射の後合成による同一化で Final を判定する。準圏の C\_\{c/\}→D\_\{F(c)/\} の弱右余終性だけを全 c に課す iff は見つからない。

:::

:::corollary "kerodon_9_1_4_7"
Kerodon Corollary 9.1.4.7（[Tag 06CR](https://kerodon.net/tag/06CR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー圏と nerve の随伴、通常圏の Final 判定はある。filtered な二準圏間の F と N(hF) の右余終性を往復する型は見つからない。

:::

:::corollary "kerodon_9_1_4_8"
Kerodon Corollary 9.1.4.8（[Tag 06CS](https://kerodon.net/tag/06CS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準写像 C→N(hC) は通常の nerve 随伴の単位として取れる。filtered な C についてこの単位の右余終性を示す型は見つからない。

:::

:::corollary "kerodon_9_1_4_9"
Kerodon Corollary 9.1.4.9（[Tag 06CT](https://kerodon.net/tag/06CT)）。対応表の状態：なし。

Monotone.final\_functor\_iffは通常圏のFinalの型。原文のnerve上のright/weakly right cofinal性との同じ射の比較が引用にない。

宣言：`Monotone.final_functor_iff`

:::

:::proposition "kerodon_9_1_4_13" (uses := "kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_5_1_4_1, kerodon_7_2_3_1, kerodon_9_1_1_16, kerodon_9_1_1_17, kerodon_9_1_3_14")
Kerodon Proposition 9.1.4.13（[Tag 06CX](https://kerodon.net/tag/06CX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既知の右余終写像を左ファイブレーションに沿って引き戻す結果と、coslice 判定はある。filtered な全空間と底を持つ任意の cocartesian ファイブレーション自身を右余終とする型は見つからない。

:::

:::corollary "kerodon_9_1_4_14" (uses := "kerodon_1_4_0_1, kerodon_7_2_1_5, kerodon_9_1_1_17, kerodon_9_1_3_2, kerodon_9_1_4_13")
Kerodon Corollary 9.1.4.14（[Tag 06CY](https://kerodon.net/tag/06CY)）。対応表の状態：一部。

isWeaklyContractible\_of\_isFilteredInfinityは同じCについて(1)⇒(3)を直接返す。原文の三条件の残りの含意は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence`

:::

:::corollary "kerodon_9_1_4_15" (uses := "kerodon_1_4_0_1, kerodon_9_1_1_16, kerodon_9_1_4_14")
Kerodon Corollary 9.1.4.15（[Tag 06CZ](https://kerodon.net/tag/06CZ)）。対応表の状態：一部。

κ=ℵ0・有限Kに限ればisRightCofinal\_sliceUnderProjection\_of\_filteredは同じcoslice忘却射の右余終性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isRightCofinal_sliceUnderProjection_of_filtered`

:::

:::corollary "kerodon_9_1_4_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isRightCofinal_sliceUnderProjection_of_filtered")
Kerodon Corollary 9.1.4.16（[Tag 06D0](https://kerodon.net/tag/06D0)）。対応表の状態：本体にある。

仮定：Quasicategory C、IsFilteredInfinity C と有限 K からの p。原文は K=Δ⁰ の場合（Lean が弱い）。結論：sliceUnderProjection p が IsRightCofinal。K=Δ⁰ で指定の coslice 忘却関手（原文に一致）。

:::

:::proposition "kerodon_9_1_4_17" (uses := "kerodon_1_4_0_1, kerodon_7_2_1_5, kerodon_7_2_1_6, kerodon_7_2_3_10, kerodon_9_1_1_17, kerodon_9_1_4_14")
Kerodon Proposition 9.1.4.17（[Tag 06D1](https://kerodon.net/tag/06D1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：両因子が右余終なら合成も右余終で、前の因子が右余終なら後ろの因子を消去で判定できる。filtered 準圏間の左ファイブレーション G を後ろに置き、合成から F の右余終性を反映する型は見つからない。

:::

:::corollary "kerodon_9_1_4_18" (uses := "kerodon_1_4_0_1, kerodon_9_1_4_15, kerodon_9_1_4_17")
Kerodon Corollary 9.1.4.18（[Tag 06D2](https://kerodon.net/tag/06D2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい q の coslice 自体の κ-filtered 性と、左ファイブレーションに沿う右余終性の基底変更はある。異なる準圏の q と F∘q の coslice 間で誘導される F\_\{q/\} が右余終となる型は見つからない。

:::

:::corollary "kerodon_9_1_4_19" (uses := "kerodon_1_4_0_1, kerodon_9_1_4_18")
Kerodon Corollary 9.1.4.19（[Tag 06D3](https://kerodon.net/tag/06D3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ filtered 準圏への coslice 射影の右余終性と、通常の structured arrow での二つの Final 関手による後合成はある。F に沿った C\_\{c/\}→D\_\{F(c)/\} 自体の右余終性は見つからない。

:::

# 9.1.5 Filtered Colimits of Spaces

%%%
number := false
tag := "kerodon-9-1-5"
%%%

Kerodon [Tag 05XR](https://kerodon.net/tag/05XR)

:::theorem "kerodon_9_1_5_1"
Kerodon Theorem 9.1.5.1（[Tag 05XS](https://kerodon.net/tag/05XS)）。対応表の状態：一部。

coherentFilteredLimitExchangeShape\_finiteは同じfiltered Cの点ごとの余極限を取る写像が任意有限形状の極限錐を保存することを直接返す。filtered性を戻す逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredLimitExchangeShape_finite`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchangeShape`

:::

:::proposition "kerodon_9_1_5_2"
Kerodon Proposition 9.1.5.2（[Tag 06D5](https://kerodon.net/tag/06D5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限形状に対する filtered 準圏の定値図式の右余終性と、通常圏での有限極限との比較から filtered 性を得る結果はある。空間値の特定 Kᵒᵖ 形状について交換を仮定して C→Fun(K,C) を右余終とする型は見つからない。

:::

:::definition "kerodon_9_1_5_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_3_9, kerodon_7_4_3_1, kerodon_8_4_2_8")
Kerodon Variant 9.1.5.4（[Tag 05XP](https://kerodon.net/tag/05XP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ-filtered 性と κ-small な形状を入力して定値図式を右余終にする型はある。κ・λ・μ の三濃度の下で S\_\{\<μ\} の交換を仮定して右余終性を得る型は見つからない。

:::

:::lemma_ "kerodon_9_1_5_6" (uses := "kerodon_1_4_0_1, kerodon_9_1_1_17, kerodon_9_1_3_2, kerodon_9_1_3_12")
Kerodon Lemma 9.1.5.6（[Tag 05XV](https://kerodon.net/tag/05XV)）。対応表の状態：一部。

中間底Ctildeもfilteredと仮定するとfiberProductToProductの右余終性と弱同値性により、二つの弱可縮な全空間の積と同じfiber productの弱可縮性を直接移せる。中間底の弱可縮性だけからの議論は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberProductToProduct_isRightCofinal`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.totalKanProductComparison_isWeakHomotopyEquivalence`

:::

:::proposition "kerodon_9_1_5_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_2_5_1, kerodon_4_2_5_4, kerodon_5_1_7_16, kerodon_5_6_0_6, kerodon_7_4_1_16, kerodon_7_4_3_6, kerodon_7_6_2_42, kerodon_7_7_7_4, kerodon_9_1_1_17, kerodon_9_1_1_18, kerodon_9_1_5_4, kerodon_9_1_5_6")
Kerodon Proposition 9.1.5.7（[Tag 05XW](https://kerodon.net/tag/05XW)）。対応表の状態：一部。

本体の対角右余終性は同じCについて(1)⇒(2)を直接返す。Archiveの逆向きと数値λ値の交換条件は採用しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_of_filtered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredLimitExchangeShape_finite`

:::

:::theorem "kerodon_9_1_5_9"
Kerodon Theorem 9.1.5.9（[Tag 05Y0](https://kerodon.net/tag/05Y0)）。対応表の状態：一部。

正則κとcardinal change boundを備え、極限形状をμ-small posetのnerveに限ると同じfiltered余極限の極限保存を直接返す。全μ-small単体形状と逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinalFilteredLimitExchangeShape_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentCardinalFilteredLimitExchange_poset`

:::

:::proposition "kerodon_9_1_5_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_4_3_6, kerodon_7_7_7_4, kerodon_9_1_1_17, kerodon_9_1_1_18, kerodon_9_1_3_2, kerodon_9_1_3_12, kerodon_9_1_5_4, kerodon_9_1_5_7")
Kerodon Proposition 9.1.5.10（[Tag 05Y1](https://kerodon.net/tag/05Y1)）。対応表の状態：一部。

κを正則に強めると同じ全κ-small Kの対角右余終性、すなわち(1)⇒(2)が直接得られる。残りの同値条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_of_kappaFiltered`

:::

:::corollary "kerodon_9_1_5_12"
Kerodon Corollary 9.1.5.12（[Tag 05Y2](https://kerodon.net/tag/05Y2)）。対応表の状態：一部。

κ≤κ+をisKappaFiltered\_of\_leに入れると同じCのκ+-filtered⇒κ-filteredを直接得る。特異性による逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_le`

:::

:::corollary "kerodon_9_1_5_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_2_8, kerodon_7_7_7_1, kerodon_9_1_5_10")
Kerodon Corollary 9.1.5.13（[Tag 0619](https://kerodon.net/tag/0619)）。対応表の状態：なし。

IsCardinalFiltered.of\_finalは通常圏のFinalによる保存。原文の∞圏のκ-filtered性とright cofinal性への比較が引用にない。

宣言：`CategoryTheory.IsCardinalFiltered.of_final`

:::

:::corollary "kerodon_9_1_5_14" (uses := "kerodon_1_4_0_1, kerodon_9_1_4_14, kerodon_9_1_5_13")
Kerodon Corollary 9.1.5.14（[Tag 06D6](https://kerodon.net/tag/06D6)）。対応表の状態：なし。

IsFiltered.of\_finalは通常圏の型であり、原文のleft fibrationの同じ三条件に含意を与えるためのnerveとcofinal性の比較を引用に持たない。

宣言：`CategoryTheory.IsFiltered.of_final`

:::

:::corollary "kerodon_9_1_5_15" (uses := "kerodon_1_4_0_1, kerodon_6_3_1_9, kerodon_7_2_1_10, kerodon_9_1_5_13")
Kerodon Corollary 9.1.5.15（[Tag 061A](https://kerodon.net/tag/061A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー retract への κ-filtered 性の移送と任意の局所化の述語はある。任意の W の局所化へ有限または κ-small 図式の余錐を送る型は見つからない。

:::

:::corollary "kerodon_9_1_5_16" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_7_4_5_1, kerodon_9_1_3_11, kerodon_9_1_5_15")
Kerodon Corollary 9.1.5.16（[Tag 061B](https://kerodon.net/tag/061B)）。対応表の状態：なし。

isKappaFiltered\_of\_strict\_isColimitはSSet内の通常余極限。原文の指定QC内の∞余極限との比較を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_strict_isColimit`

:::

:::corollary "kerodon_9_1_5_17"
Kerodon Corollary 9.1.5.17（[Tag 06D7](https://kerodon.net/tag/06D7)）。対応表の状態：なし。

通常圏のFinalによるκ-filtered性の移送は、原文の同じ∞部分圏包含のright cofinal性との比較がない。

宣言：`CategoryTheory.IsCardinalFiltered.of_final`

:::

:::proposition "kerodon_9_1_5_18"
Kerodon Proposition 9.1.5.18（[Tag 02QC](https://kerodon.net/tag/02QC)）。対応表の状態：なし。

指定されたC自体のQC内の余極限表示ではなく、Cとcodiscrete nerveの積の通常SSet余極限表示。両方の比較を追加しない限り同じ結論成分でない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamilyCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamily_isCardinalFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_strict_isColimit`

:::

# 9.1.6 Filtered Colimits of Simplicial Sets

%%%
number := false
tag := "kerodon-9-1-6"
%%%

Kerodon [Tag 03DD](https://kerodon.net/tag/03DD)

:::proposition "kerodon_9_1_6_1" (uses := "kerodon_1_1_0_6, kerodon_4_8_8_11, kerodon_7_5_6_1, kerodon_7_5_8_2, kerodon_7_5_8_6, kerodon_7_5_8_7, kerodon_9_1_6_7")
Kerodon Proposition 9.1.6.1（[Tag 03DE](https://kerodon.net/tag/03DE)）。対応表の状態：なし。

通常filtered余極限の準圏性や自然変換上の弱同値保存は、原文の同じ余錐がcategorical colimit diagramとなる結論を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.quasicategory_of_filtered_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.filteredColimitMap_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.filteredColimitMap_isWeakHomotopyEquivalence`

:::

:::corollary "kerodon_9_1_6_3" (uses := "kerodon_1_4_0_1, kerodon_7_5_8_9, kerodon_9_1_6_1")
Kerodon Corollary 9.1.6.3（[Tag 03DG](https://kerodon.net/tag/03DG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な単体集合の filtered 余極限の準圏性と、Kan 複体の厳密な余錐の比較はある。通常の QCat の nerve から coherent nerve QC への包含が filtered 余極限を保つ型は見つからない。

:::

:::definition "kerodon_9_1_6_4"
Kerodon Variant 9.1.6.4（[Tag 03DH](https://kerodon.net/tag/03DH)）。対応表の状態：一部。

同じKan値図式について、忘却した単体集合の指定余錐が通常余極限でもあると追加するとstrictNativeCocone\_isColimit\_of\_filtered\_forgetは同じ余錐のSpace内余極限性を直接返す。Kan圏での通常余極限という入力だけから忘却後の余極限性を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.filteredColimitMap_isWeakHomotopyEquivalence`、`SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_filtered`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.filteredColimit_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget`

:::

:::corollary "kerodon_9_1_6_6"
Kerodon Corollary 9.1.6.6（[Tag 03DJ](https://kerodon.net/tag/03DJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：添字形状の通常余極限から切断空間の極限を得る型と、左ファイブレーションから空間の余極限を作る型はある。任意の D と G で各 F(c) と N(C) の余極限の存在・保存を K へ移す結論は見つからない。

:::

:::proposition "kerodon_9_1_6_7" (uses := "kerodon_1_1_0_6, kerodon_7_5_6_1, kerodon_9_1_6_12")
Kerodon Proposition 9.1.6.7（[Tag 03DL](https://kerodon.net/tag/03DL)）。対応表の状態：一部。

ModelCategoryと生成系・局所表示可能性など射影モデル構造の入力を置くと、射影モデル構造の分解により同じ図式へのcofibrant置換と各点trivial fibrationを得る。SSetに具体的ModelCategory instanceなし。

宣言：`SerrePositivity.DiagramModel.Projective.modelCategory`、`SerrePositivity.DiagramModel.Projective.modelCategory_generated`

:::

:::definition "kerodon_9_1_6_8"
Kerodon Definition 9.1.6.8（[Tag 03DM](https://kerodon.net/tag/03DM)）。対応表の状態：なし。

modelCategoryとcofibrations\_le\_objectwiseは射影cofibrationの各点cofibration性で、原文の全各点trivial Kan fibrationに対する同じLLPの定義との比較を型に含まない。

宣言：`SerrePositivity.DiagramModel.Projective.modelCategory`、`SerrePositivity.DiagramModel.Projective.cofibrations_le_objectwise`、`SerrePositivity.DiagramModel.Projective.generators`

:::

:::proposition "kerodon_9_1_6_12"
Kerodon Proposition 9.1.6.12（[Tag 03DR](https://kerodon.net/tag/03DR)）。対応表の状態：一部。

射影モデル構造のModelCategory・生成系等を入力すると同じ自然変換をcofibrationと各点trivial fibrationへ分解できる。SSetへの具体的instanceなし、一般schemaとしての条件つき対応。

宣言：`SerrePositivity.DiagramModel.Projective.modelCategory`

:::

:::corollary "kerodon_9_1_6_13"
Kerodon Corollary 9.1.6.13（[Tag 03DS](https://kerodon.net/tag/03DS)）。対応表の状態：なし。

一般生成系からの射影モデル構造は、原文の具体的∂Δn×hCによる最小弱飽和閉包との比較を型に含まない。

宣言：`SerrePositivity.DiagramModel.Projective.modelCategory_generated`、`SerrePositivity.DiagramModel.Projective.generators`、`SerrePositivity.DiagramModel.Projective.cofibrations_le_objectwise`

:::

# 9.1.7 Approximation by Simplicial Subsets

%%%
number := false
tag := "kerodon-9-1-7"
%%%

Kerodon [Tag 061E](https://kerodon.net/tag/061E)

:::proposition "kerodon_9_1_7_1"
Kerodon Proposition 9.1.7.1（[Tag 061F](https://kerodon.net/tag/061F)）。対応表の状態：一部。

λを正則にも強めるとinnerHornClosureの包含・準圏性・濃度上界が同じC0の小準圏への拡大を直接与える。非正則λは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.hasCardinalLT_innerHornClosure`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinal_innerHornClosure_lt`

:::

:::corollary "kerodon_9_1_7_2"
Kerodon Corollary 9.1.7.2（[Tag 061G](https://kerodon.net/tag/061G)）。対応表の状態：一部。

準圏性をPに取りinnerHornClosureの小性と包含を渡すと、smallSubcomplexFamilyの同じ小準圏族のλ-filtered性と通常SSet余極限表示を直接得る。QC内の余極限表示は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamily_isCardinalFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.hasCardinalLT_innerHornClosure`

:::

:::proposition "kerodon_9_1_7_3"
Kerodon Proposition 9.1.7.3（[Tag 061H](https://kerodon.net/tag/061H)）。対応表の状態：なし。

posetの部分集合の小性だけでは、そのnerveの全非退化単体のλ-small性への比較がなく、原文の小単体部分集合の拡大を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing`、`Cardinal.SharplyLT.exists_isCardinalFiltered_set`

:::

:::corollary "kerodon_9_1_7_4"
Kerodon Corollary 9.1.7.4（[Tag 061J](https://kerodon.net/tag/061J)）。対応表の状態：なし。

posetの部分集合族の被覆とfiltered性は、原文の単体部分集合の濃度・SSet余極限・QC余極限を同じ対象に対して返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_cover`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered`

:::

:::definition "kerodon_9_1_7_5"
Kerodon Definition 9.1.7.5（[Tag 061K](https://kerodon.net/tag/061K)）。対応表の状態：一部。

SharplyLTとexists\_cofinalは厳密κ◁λについて同じ小部分集合のcofinal族の条件を直接与える。非厳密κ⊴λの等号の場合を含む全定義はこの引用だけに含まない。

宣言：`Cardinal.SharplyLT`、`Cardinal.SharplyLT.tfae`、`Cardinal.SharplyLT.exists_cofinal`

:::

:::proposition "kerodon_9_1_7_8"
Kerodon Proposition 9.1.7.8（[Tag 061N](https://kerodon.net/tag/061N)）。対応表の状態：一部。

Cardinal.SharplyLT.of\_pow\_ltは原文の指数条件を同じ基数に適用して最後のκ◁λを直接返す。全κ-small部分集合族自体のλ-small性の成分は含まない。

宣言：`Cardinal.SharplyLT.of_pow_lt`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound.sharplyLT`

:::

:::corollary "kerodon_9_1_7_9"
Kerodon Corollary 9.1.7.9（[Tag 061P](https://kerodon.net/tag/061P)）。対応表の状態：一部。

κ\<λに限るとof\_pow\_ltは同じκ◁λを返すのでκ⊴λの要求を満たす。κ=λの場合は引用の型外。

宣言：`Cardinal.SharplyLT.of_pow_lt`

:::

:::proposition "kerodon_9_1_7_12"
Kerodon Proposition 9.1.7.12（[Tag 061S](https://kerodon.net/tag/061S)）。対応表の状態：一部。

同じκ\<λの指数条件からof\_pow\_ltがκ◁λを直接返す。GCHを使う逆向きは含まない。

宣言：`Cardinal.SharplyLT.of_pow_lt`

:::

:::proposition "kerodon_9_1_7_13"
Kerodon Proposition 9.1.7.13（[Tag 061T](https://kerodon.net/tag/061T)）。対応表の状態：一部。

κ\<λ\<μに限ればSharplyLT.transが同じκ◁μを返す。等号を許す非厳密版全体は含まない。

宣言：`Cardinal.SharplyLT.trans`

:::

:::proposition "kerodon_9_1_7_14"
Kerodon Proposition 9.1.7.14（[Tag 061U](https://kerodon.net/tag/061U)）。対応表の状態：なし。

通常posetの部分集合のλ-small性とκ-directed性は、そのnerveの小性と∞filtered性の同時比較を型に含まず、原文の指定単体部分集合の拡大は直接得られない。

宣言：`Cardinal.SharplyLT.exists_isCardinalFiltered_set`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing`

:::

:::corollary "kerodon_9_1_7_16"
Kerodon Corollary 9.1.7.16（[Tag 061W](https://kerodon.net/tag/061W)）。対応表の状態：なし。

poset被覆のfiltered性だけでは、原文の小準圏の単体的な濃度と二つの圏での余極限表示を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_cover`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered`、`Cardinal.SharplyLT.exists_isCardinalFiltered_set`

:::

:::lemma_ "kerodon_9_1_7_18"
Kerodon Lemma 9.1.7.18（[Tag 061Y](https://kerodon.net/tag/061Y)）。対応表の状態：なし。

集合の小部分集合のcofinal族は、原文の面・退化で閉じた単体部分集合族の小性との比較を含まない。

宣言：`Cardinal.SharplyLT.exists_cofinal`

:::

:::proposition "kerodon_9_1_7_20"
Kerodon Proposition 9.1.7.20（[Tag 0620](https://kerodon.net/tag/0620)）。対応表の状態：なし。

poset被覆のfiltered性と各nerveのκ-filtered性はあるが、原文のλ-smallな単体部分圏とμ-small添字の同じ余極限表示を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_cover`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPiece_nerve_isKappaFiltered`、`Cardinal.SharplyLT.exists_isCardinalFiltered_set`

:::

:::definition "kerodon_9_1_7_21"
Kerodon Variant 9.1.7.21（[Tag 0621](https://kerodon.net/tag/0621)）。対応表の状態：一部。

B6型照合：濃度変更条件を満たす filtered poset の nerve は、小さい filtered 部分 poset の nerve の通常の SSet 余極限になる。部分集合の添字の filtered 性もある。任意の μ-small 準圏の表示と、原文の λ,μ による添字の濃度境界は残る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredNerveCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPiece_nerve_properties`

:::

# 9.1.8 Approximation by Partially Ordered Sets

%%%
number := false
tag := "kerodon-9-1-8"
%%%

Kerodon [Tag 02Q8](https://kerodon.net/tag/02Q8)

:::theorem "kerodon_9_1_8_1" (uses := "kerodon_1_4_0_1")
Kerodon Theorem 9.1.8.1（[Tag 0622](https://kerodon.net/tag/0622)）。対応表の状態：一部。

B6型照合：κ=ℵ₀ として「filtered ⇒ cofinal な directed poset が存在」の向きのみ。逆向き（cofinal poset から filtered）の宣言は見当たらない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex`

:::

:::lemma_ "kerodon_9_1_8_2"
Kerodon Lemma 9.1.8.2（[Tag 02QB](https://kerodon.net/tag/02QB)）。対応表の状態：一部。

B6型照合：仮定：Lean の小部分複体の拡張には κ の正則性と κ≤\#T が必要。原文は無限基数 κ（Lean が強い）。結論：C×N(Codiscrete T)→C は非空 T で自明 Kan ファイブレーション。積で小さい単射余錐を得る宣言はあるが、任意の無限 κ に対する原文の存在は覆わない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.codiscreteProductProjection_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_small_codiscreteConeRange`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_small_terminalSubcomplex`

:::

:::lemma_ "kerodon_9_1_8_4"
Kerodon Lemma 9.1.8.4（[Tag 0624](https://kerodon.net/tag/0624)）。対応表の状態：なし。

原文の指定C自体とKα▷による表示ではなくC×N(Codiscrete T)上の終対象付き部分複体の右余終性。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexCarrierBase_isRightCofinal`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamily_isCardinalFiltered`

:::

:::proposition "kerodon_9_1_8_5"
Kerodon Proposition 9.1.8.5（[Tag 0625](https://kerodon.net/tag/0625)）。対応表の状態：なし。

C×N(Codiscrete T)の通常余極限表示は指定QC\_\<λ内のCの余極限表示と比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamilyCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamily_isCardinalFiltered`

:::

:::theorem "kerodon_9_1_8_7"
Kerodon Theorem 9.1.8.7（[Tag 02QA](https://kerodon.net/tag/02QA)）。対応表の状態：一部。

B6型照合：右 cofinal な κ-directed poset の存在は確認。κ◁λ と C の λ-small 性から、添字 poset も λ-small に取る原文の基数評価は引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_cardinalFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`

:::

:::corollary "kerodon_9_1_8_8"
Kerodon Corollary 9.1.8.8（[Tag 0627](https://kerodon.net/tag/0627)）。対応表の状態：一部。

B6型照合：「κ-filtered ⇒ cofinal な κ-directed poset が存在」の向きのみ。逆向きの宣言は見当たらない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered`

:::

:::corollary "kerodon_9_1_8_9"
Kerodon Corollary 9.1.8.9（[Tag 06D8](https://kerodon.net/tag/06D8)）。対応表の状態：なし。

任意のcofinal posetの存在は指定Ord\_\<κを始域にする存在と異なり、ordinalNerveのfiltered性だけは証明の部品。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ordinalNerve_isKappaFiltered`

:::

:::corollary "kerodon_9_1_8_10"
Kerodon Corollary 9.1.8.10（[Tag 0628](https://kerodon.net/tag/0628)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：可算個の単体を持つ X の有限段階の通常余極限と、一般の κ-directed poset からの右余終関手はある。自然数の nerve 自体から可算 filtered 準圏へ右余終関手を構成する型は見つからない。

:::

:::proposition "kerodon_9_1_8_11" (uses := "kerodon_1_4_0_1, kerodon_8_4_2_1, kerodon_8_5_5_5, kerodon_9_1_5_13")
Kerodon Proposition 9.1.8.11（[Tag 0629](https://kerodon.net/tag/0629)）。対応表の状態：一部。

終対象を持つ場合にisKappaFiltered\_of\_terminalは同じCのκ-filtered性を直接返す。原文の終対象条件からfiltered性への成分に一致し、その他の同値条件と逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemShape_isKappaFiltered`

:::

:::corollary "kerodon_9_1_8_12"
Kerodon Corollary 9.1.8.12（[Tag 062A](https://kerodon.net/tag/062A)）。対応表の状態：一部。

B6型照合：終対象 ⇒ κ-filtered の向きのみ。有限な filtered ∞ 圏が終対象を持つ向きはない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex`

:::

# 9.1.9 Filtered Colimits of ∞-Categories

%%%
number := false
tag := "kerodon-9-1-9"
%%%

Kerodon [Tag 062Y](https://kerodon.net/tag/062Y)

:::proposition "kerodon_9_1_9_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_6_5_18, kerodon_7_2_2_11, kerodon_9_1_6_3, kerodon_9_1_8_1")
Kerodon Proposition 9.1.9.1（[Tag 062Z](https://kerodon.net/tag/062Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の filtered 余極限の準圏性と空間の 0-truncated の述語はある。QC 内の余極限で写像空間の一様な n-truncation を保存する型は見つからない。

:::

:::definition "kerodon_9_1_9_3"
Kerodon Variant 9.1.9.3（[Tag 0631](https://kerodon.net/tag/0631)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の filtered 図式の正準余錐と、個別の空間の 0-truncated 述語はある。任意の整数 n で全頂点が n-truncated のとき、その空間値余極限も n-truncated となる型は見つからない。

:::

:::proposition "kerodon_9_1_9_4"
Kerodon Proposition 9.1.9.4（[Tag 042P](https://kerodon.net/tag/042P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏では walking idempotent の余極限存在によって冪等完備性を判定できる。filtered 準圏図式の QC 内の余極限でこの性質を保存する型は見つからない。

:::

:::proposition "kerodon_9_1_9_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_9_1_9_1, kerodon_9_1_9_7")
Kerodon Proposition 9.1.9.5（[Tag 0632](https://kerodon.net/tag/0632)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な κ-filtered 余極限では κ-small な図式の写像がある段で因数分解し、各段の κ-filtered 性も移る。QC 内の余極限で、遷移関手が K 余極限を保つとき各余錐脚も保つという型は見つからない。

:::

:::lemma_ "kerodon_9_1_9_6" (uses := "kerodon_1_1_0_6, kerodon_9_2_5_10")
Kerodon Lemma 9.1.9.6（[Tag 0633](https://kerodon.net/tag/0633)）。対応表の状態：なし。

κ-small写像の段への因数分解は、原文のcoslice余極限比較θの同型性とは異なる結論。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_strict_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.kappaSmall_factorization_of_isColimit`

:::

:::lemma_ "kerodon_9_1_9_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_3_17, kerodon_9_1_9_6")
Kerodon Lemma 9.1.9.7（[Tag 0634](https://kerodon.net/tag/0634)）。対応表の状態：一部。

B6型照合：指定された通常 filtered 余極限の頂点が準圏となる結論はある。互換な K▷ 図式が各段で普遍余錐なら、同じ余錐が頂点の準圏でも普遍になる型は見つからない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.quasicategory_of_filtered_isColimit`

:::

:::proposition "kerodon_9_1_9_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_9_1_9_1, kerodon_9_1_9_5, kerodon_9_2_5_10")
Kerodon Proposition 9.1.9.8（[Tag 0635](https://kerodon.net/tag/0635)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な余極限への小図式の因数分解と Kan 複体の余錐比較はある。一般の QC の余極限で K 余極限が存在し、そこから出る任意の T の保存性を全段で判定する型は見つからない。

:::

:::corollary "kerodon_9_1_9_9"
Kerodon Corollary 9.1.9.9（[Tag 0636](https://kerodon.net/tag/0636)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限を保つ射を持つ presentable 圏の模型と、関手の κ-filtered 余極限保存の述語はある。任意の形状族 K について K-余完備な準圏の部分圏に小 κ-filtered 余極限を作り包含の保存まで与える型は見つからない。

:::

:::definition "kerodon_9_1_9_10"
Kerodon Variant 9.1.9.10（[Tag 0637](https://kerodon.net/tag/0637)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：presentable 圏の PrL は一宇宙の全小余極限保存を用い、strict な補題は単体集合の余極限の filtered 性を扱う。非可算 λ で QC\_\{\<λ\} の K-余完備部分に λ-small な余極限を作る型は見つからない。

:::

:::corollary "kerodon_9_1_9_11"
Kerodon Corollary 9.1.9.11（[Tag 0638](https://kerodon.net/tag/0638)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限保存から κ-finitary 性を得る型と特定の Ind 左 Kan 延長の保存性はある。指数余終性の下で任意の K-余完備化関手が λ-small κ-filtered 余極限を保つ型は見つからない。

:::

