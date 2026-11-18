import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Order.CompleteLattice.Defs
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFunctorTheorem
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrInfinity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "9.5 Presentable ∞-Categories" =>
%%%
number := false
tag := "kerodon-9-5"
%%%

Kerodon の 9.5 節（[Tag 06NC](https://kerodon.net/tag/06NC)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_9_5_0_1" (lean := "isLUB_sSup")
Kerodon Proposition 9.5.0.1（[Tag 06PT](https://kerodon.net/tag/06PT)）。対応表の状態：Mathlib にある。

仮定：CompleteSemilatticeSup と任意の部分集合 s。原文は完備束なので下限も持つ（Lean が弱い）。結論：isLUB\_sSup s は sSup s が s の最小上界であること（原文と一致）。

:::

# 9.5.1 Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-1"
%%%

Kerodon [Tag 06NE](https://kerodon.net/tag/06NE)

:::theorem "kerodon_9_5_1_1"
Kerodon Theorem 9.5.1.1（[Tag 06PU](https://kerodon.net/tag/06PU)）。対応表の状態：一部。

accessibleかつcocompleteはIsPresentableの定義そのもので、hasSmallLimitsは同じCの完備性を直接返す。complete⇒cocompleteは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits`

:::

:::definition "kerodon_9_5_1_2" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
Kerodon Definition 9.5.1.2（[Tag 06ND](https://kerodon.net/tag/06ND)）。対応表の状態：本体にある。

仮定：Quasicategory C（Kerodon と一致）。結論：IsPresentable C は IsAccessible と HasSmallColimits の連言（原文の accessible かつ余完備と一致）。

:::

:::theorem "kerodon_9_5_1_8"
Kerodon Theorem 9.5.1.8（[Tag 06PY](https://kerodon.net/tag/06PY)）。対応表の状態：一部。

IsPresentableの同じCと同じFにpresentableContinuous\_isRepresentableを適用して小極限保存⇒表現可能を直接得る。逆向きはこの引用に含まない。

宣言：`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable`

:::

:::theorem "kerodon_9_5_1_9"
Kerodon Theorem 9.5.1.9（[Tag 06PZ](https://kerodon.net/tag/06PZ)）。対応表の状態：一部。

accessible\_preservesLimits\_isCorepresentableは同じC,Fについてaccessibleかつ全小極限保存⇒corepresentableを直接返す。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable`

:::

:::proposition "kerodon_9_5_1_11"
Kerodon Proposition 9.5.1.11（[Tag 06Q1](https://kerodon.net/tag/06Q1)）。対応表の状態：なし。

固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheaf_isRepresentable_of_sendsSmallColimitsToLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableContinuous_isRepresentable_of_inversionLocality`

:::

:::corollary "kerodon_9_5_1_12"
Kerodon Corollary 9.5.1.12（[Tag 06UE](https://kerodon.net/tag/06UE)）。対応表の状態：一部。

Cをpresentableにも強め、Kを宇宙小形状に限るとhasSmallLimitsの同じKへの適用が原文の同じCのK極限の存在を直接返す。二濃度の入力だけの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits`

:::

:::proposition "kerodon_9_5_1_13"
Kerodon Proposition 9.5.1.13（[Tag 06Q2](https://kerodon.net/tag/06Q2)）。対応表の状態：なし。

固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable`

:::

# 9.5.2 The Adjoint Functor Theorem

%%%
number := false
tag := "kerodon-9-5-2"
%%%

Kerodon [Tag 06Q4](https://kerodon.net/tag/06Q4)

:::theorem "kerodon_9_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
Kerodon Theorem 9.5.2.1（[Tag 06Q5](https://kerodon.net/tag/06Q5)）。対応表の状態：本体にある。

仮定：C,D が quasicategory で IsPresentable、指定した F または G（Kerodon と一致）。結論：右随伴の存在と小余極限保存の iff、左随伴の存在と accessible 性かつ小極限保存の iff（原文の二主張と一致）。

:::

:::proposition "kerodon_9_5_2_2"
Kerodon Proposition 9.5.2.2（[Tag 06QB](https://kerodon.net/tag/06QB)）。対応表の状態：一部。

Dをaccessibleにも強め、presentableなCからの全連続前層の表現定理をhRepへ入れると、native判定は同じFの右随伴存在と全小余極限保存のiffを直接返す。Dをpresentableとする必要はなく、局所小だけの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native`

:::

:::proposition "kerodon_9_5_2_3"
Kerodon Proposition 9.5.2.3（[Tag 06QC](https://kerodon.net/tag/06QC)）。対応表の状態：一部。

Dをpresentableとする原文の仮定の下でrightAdjoint\_isAccessibleとadjunction\_preservesSmallLimitsは同じGの左随伴存在⇒accessibleかつ小極限保存を直接与える。引用のiffが要求するCのpresentabilityは逆向きに限る追加入力。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible`

:::

:::definition "kerodon_9_5_2_5"
Kerodon Variant 9.5.2.5（[Tag 06QE](https://kerodon.net/tag/06QE)）。対応表の状態：なし。

全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits`

:::

:::definition "kerodon_9_5_2_6"
Kerodon Variant 9.5.2.6（[Tag 06QF](https://kerodon.net/tag/06QF)）。対応表の状態：なし。

全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_of_accessible_limitPreserving_HomModels`

:::

# 9.5.3 The ∞-Category of Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-3"
%%%

Kerodon [Tag 06UF](https://kerodon.net/tag/06UF)

:::definition "kerodon_9_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrL")
Kerodon Construction 9.5.3.1（[Tag 06PF](https://kerodon.net/tag/06PF)）。対応表の状態：本体にある。

仮定：外部の圏の仮定なし。PrL の対象は小余極限を持つ accessible quasicategory（Kerodon と一致）。結論：coherent nerve PrL の写像空間は小余極限保存関手の充満関手空間の core（原文の指定の射と一致）。

:::

:::definition "kerodon_9_5_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrR")
Kerodon Variant 9.5.3.2（[Tag 06UG](https://kerodon.net/tag/06UG)）。対応表の状態：本体にある。

仮定：外部の圏の仮定なし。対象は presentable な quasicategory（Kerodon と一致）。結論：coherent nerve PrR の写像空間は accessible かつ小極限を保存する関手空間の core（原文の指定の射と一致）。

:::

:::definition "kerodon_9_5_3_5"
Kerodon Definition 9.5.3.5（[Tag 06PK](https://kerodon.net/tag/06PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の presentable 圏と、大域的な余カルテシアン射の輸送および小余極限保存はある。任意の局所余カルテシアン射の全ファイバー・全輸送に原文の条件を束ねる述語は未確認。

:::

:::proposition "kerodon_9_5_3_7"
Kerodon Proposition 9.5.3.7（[Tag 06UJ](https://kerodon.net/tag/06UJ)）。対応表の状態：なし。

固定された二つのpresentable圏の随伴存在判定は、原文のUのlocally cartesian/cocartesian性とその輸送関手への同一視を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`

:::

:::corollary "kerodon_9_5_3_8"
Kerodon Corollary 9.5.3.8（[Tag 06Q8](https://kerodon.net/tag/06Q8)）。対応表の状態：なし。

PrL/PrRの構成と固定二対象の随伴同値は、原文の指定Uの輸送表現の因数分解とファイブレーション性の四条件を結ぶ型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrL`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrR`

:::

:::corollary "kerodon_9_5_3_9"
Kerodon Corollary 9.5.3.9（[Tag 06Q9](https://kerodon.net/tag/06Q9)）。対応表の状態：なし。

固定二対象のpresentableAdjointFunctorEquivalenceは、原文の準圏そのものを動かす全PrLop→PrRの指定Ψとは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`

:::

# 9.5.4 Closure Properties of Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-4"
%%%

Kerodon [Tag 06P5](https://kerodon.net/tag/06P5)

:::proposition "kerodon_9_5_4_1"
Kerodon Proposition 9.5.4.1（[Tag 06P6](https://kerodon.net/tag/06P6)）。対応表の状態：なし。

generatedSourceCategoryのpresentabilityは、指定slice/coslice準圏全体との同一視を引用に持たない。通常Overのaccessible性も別の模型。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_isPresentable`、`CategoryTheory.Over.instIsAccessibleCategory`、`CategoryTheory.Under.instIsAccessibleCategory`

:::

:::corollary "kerodon_9_5_4_2"
Kerodon Corollary 9.5.4.2（[Tag 06UK](https://kerodon.net/tag/06UK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib には通常圏の普遍余極限と指数可能性の述語があり、厳密な単体集合の slice には右随伴がある。presentable な準圏で局所カルテシアン閉性と全・小普遍余極限を同値にする型は未確認。

:::

:::proposition "kerodon_9_5_4_3"
Kerodon Proposition 9.5.4.3（[Tag 06P7](https://kerodon.net/tag/06P7)）。対応表の状態：一部。

Kを小準圏に限るとfunctor\_isPresentableが同じFun(K,C)のpresentabilityを直接返す。任意の単体集合Kは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`

:::

:::proposition "kerodon_9_5_4_4" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_5, kerodon_9_4_9_4")
Kerodon Proposition 9.5.4.4（[Tag 06P8](https://kerodon.net/tag/06P8)）。対応表の状態：なし。

Arrow(C)のpresentabilityは原文の指定F−,F+のoriented fiber productとの比較を持たない。恒等の特殊化でも指定模型との比較が未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.arrow_isPresentable`、`CategoryTheory.Comma.isAccessibleCategory`、`SerrePositivity.Smith.arrow_locallyPresentable`

:::

:::corollary "kerodon_9_5_4_6" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 9.5.4.6（[Tag 06PA](https://kerodon.net/tag/06PA)）。対応表の状態：一部。

両脚cocontinuous、一方equivalence lifting、strict pullback模型に限りpullback\_isAccessibleを入力してisPresentable\_of\_isAccessibleを適用すると同じ全空間のpresentabilityを直接得る。continuous側と任意の指定模型は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_isPresentable_of_accessiblePullback`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isPresentable_of_isAccessible`

:::

:::proposition "kerodon_9_5_4_7"
Kerodon Proposition 9.5.4.7（[Tag 06PC](https://kerodon.net/tag/06PC)）。対応表の状態：なし。

積・pullback・関手準圏のpresentabilityを、原文の指定QC内の一般図式の極限と同一視する型を引用に持たない。各構成を組む議論だけをpartialとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_isPresentable_of_accessiblePullback`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`

:::

:::definition "kerodon_9_5_4_10"
Kerodon Variant 9.5.4.10（[Tag 06UL](https://kerodon.net/tag/06UL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の補題は余極限を保つ脚を要求し、strict な単体集合の小極限の補題は filtered 余極限との交換までを与える。小さい任意形状の accessible な極限保存関手の図式の極限が presentable となる型は見つからない。

:::

:::proposition "kerodon_9_5_4_12"
Kerodon Proposition 9.5.4.12（[Tag 06PH](https://kerodon.net/tag/06PH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の模型と個別の積・引戻しの presentability を確認した。これらは PrL・PrR 内の任意の小極限も、QC\_\{≤Ω\} への包含での保存も与えない。

:::

:::corollary "kerodon_9_5_4_13"
Kerodon Corollary 9.5.4.13（[Tag 06UN](https://kerodon.net/tag/06UN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の準圏模型と単独の presentable 圏の小極限存在はある。PrL と PrR 自体への小余極限の存在を与える型は見つからない。

:::

:::proposition "kerodon_9_5_4_17"
Kerodon Proposition 9.5.4.17（[Tag 06PN](https://kerodon.net/tag/06PN)）。対応表の状態：なし。

全関手準圏のpresentabilityと評価保存は、原文のUのsection準圏と同じものへの比較がない。積束に限るだけで同じ指定対象と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseCompactHom.evaluateFunctorAt_preservesSmallColimits`

:::

:::lemma_ "kerodon_9_5_4_19"
Kerodon Lemma 9.5.4.19（[Tag 06PQ](https://kerodon.net/tag/06PQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余 cartesian 切断の部分空間と coslice の κ-filtered 余極限はある。各頂点が presentable で辺ごとに accessible な局所 (co)cartesian ファイブレーションの切断圏を presentable とする型は見つからない。

:::

# 9.5.5 Cocontinuous Functors

%%%
number := false
tag := "kerodon-9-5-5"
%%%

Kerodon [Tag 06US](https://kerodon.net/tag/06US)

:::definition "kerodon_9_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
Kerodon Definition 9.5.5.1（[Tag 06NF](https://kerodon.net/tag/06NF)）。対応表の状態：本体にある。

同じCのIsPresentable CとIsKappaAccessible κ Cの論理積が原文のκ-presentableの定義全体を直接表す。専用名がないことは不足としない。

:::

:::proposition "kerodon_9_5_5_3"
Kerodon Proposition 9.5.5.3（[Tag 06NM](https://kerodon.net/tag/06NM)）。対応表の状態：なし。

isPresentable\_iff\_cocompleteIndEquivalenceはある基数の存在であり、原文の指定κに固定した小さいκ余完備な生成圏の表示を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_cocompleteIndEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indInfinity_isPresentable_iff_hasSmallColimits`

:::

:::proposition "kerodon_9_5_5_5"
Kerodon Proposition 9.5.5.5（[Tag 06NP](https://kerodon.net/tag/06NP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と前層余完備化への左 Kan 延長を確認した。κ-余完備化を相対 Ind\_\{κ\}\^\{λ\} に入れた合成が λ-余完備化になる主張は未確認。

:::

:::corollary "kerodon_9_5_5_6"
Kerodon Corollary 9.5.5.6（[Tag 06NQ](https://kerodon.net/tag/06NQ)）。対応表の状態：なし。

Indのκ-filtered余極限存在だけでは指定λ-small全余極限存在は出ない。通常圏Indの全余極限存在はnerve比較なし。

宣言：`CategoryTheory.instHasColimitsIndOfHasFiniteColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits`

:::

:::corollary "kerodon_9_5_5_7"
Kerodon Corollary 9.5.5.7（[Tag 06NR](https://kerodon.net/tag/06NR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：コンパクト対象の有限余極限閉性と小準圏形状での結果はある。二濃度の生成のもとで C の λ-余完備性、κ-余完備性、compact 部分の κ-余完備性を相互に導く型は未確認。

:::

:::corollary "kerodon_9_5_5_8"
Kerodon Corollary 9.5.5.8（[Tag 06NS](https://kerodon.net/tag/06NS)）。対応表の状態：一部。

κ=ℵ0としCが有限余極限を持つ場合、hasFiniteColimits\_kappaCompactObjectsは同じcompact対象部分圏の有限余極限存在、すなわち(2)⇒(3)を直接返す。全iffと任意κは含まない。

宣言：`CategoryTheory.instHasColimitsIndOfHasFiniteColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasFiniteColimits_kappaCompactObjects`

:::

:::proposition "kerodon_9_5_5_9"
Kerodon Proposition 9.5.5.9（[Tag 06NU](https://kerodon.net/tag/06NU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda に沿う左 Kan 延長が小 κ-filtered 余極限を保つ型はある。原文が比較する元の f と拡張 F の κ・λ 右完全性は異なる形状の条件であり、その三条件の同値は未確認。

:::

:::corollary "kerodon_9_5_5_10"
Kerodon Corollary 9.5.5.10（[Tag 06NV](https://kerodon.net/tag/06NV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存から κ-filtered 保存への含意と、Ind 延長の同種の保存を確認した。元の f の κ-小余極限保存から F の λ-小な全余極限保存を導く、二濃度の iff は未確認。

:::

:::corollary "kerodon_9_5_5_11"
Kerodon Corollary 9.5.5.11（[Tag 06NW](https://kerodon.net/tag/06NW)）。対応表の状態：なし。

Indのκ-filtered余極限保存関手の制限同値は、原文の全λ-small余極限保存関手への同じ制限ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::corollary "kerodon_9_5_5_12"
Kerodon Corollary 9.5.5.12（[Tag 06Z9](https://kerodon.net/tag/06Z9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0 切断、有限模型による全空間の生成、全関手圏の presentability を確認した。S\^\{≤n\}\_fin 上の有限余極限保存関手の Δ⁰ 評価の充満忠実性と n-余切断対象による本質像は未確認。

:::

:::corollary "kerodon_9_5_5_13"
Kerodon Corollary 9.5.5.13（[Tag 06NX](https://kerodon.net/tag/06NX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存が κ-filtered 保存を含む向きはある。二濃度で、finitary 性と compact 部分の κ-余連続性から任意の λ-小余極限保存を復元する向きは未確認。

:::

:::corollary "kerodon_9_5_5_14"
Kerodon Corollary 9.5.5.14（[Tag 06NY](https://kerodon.net/tag/06NY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と compact 生成モデルはある。原文の C の λ-余連続関手を C\_\{\<κ\} 上の κ-余連続関手へ送る、全ての小形状に関する制限同値は未確認。

:::

:::corollary "kerodon_9_5_5_15"
Kerodon Corollary 9.5.5.15（[Tag 06NZ](https://kerodon.net/tag/06NZ)）。対応表の状態：一部。

Cを標準Indκ(A)に限り同じFが左Kan拡張である場合、indLeftKanExtension\_preservesSmallKappaFilteredColimitsは原文右辺の同じFのκ-finitary成分を直接返す。compact部分への保存条件と全iffは含まない。

宣言：`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isKappaAccessibleFunctor`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits`

:::

:::corollary "kerodon_9_5_5_16"
Kerodon Corollary 9.5.5.16（[Tag 06ZA](https://kerodon.net/tag/06ZA)）。対応表の状態：なし。

PrLFunctorSpaceの準圏性と全Fun(K,D)のpresentabilityは、cocontinuous全部分圏自身のpresentabilityを返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.prLFunctorSpace_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`

:::

:::proposition "kerodon_9_5_5_17"
Kerodon Proposition 9.5.5.17（[Tag 06P0](https://kerodon.net/tag/06P0)）。対応表の状態：一部。

IsPresentableの同じCの局所小性と全小余極限存在は原文の右辺(a)(b)を直接返す。小生成族の全余極限生成と全対象のcompact基数はこの引用だけでは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable.hasSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaCompactGenerating.exists_smallFamilyPresentation`

:::

:::lemma_ "kerodon_9_5_5_18"
Kerodon Lemma 9.5.5.18（[Tag 06P1](https://kerodon.net/tag/06P1)）。対応表の状態：一部。

数値λ制限のない標準Indκの小始域の場合、indComparison\_isFullyFaithful\_of\_compactは同じhのκ-finitary拡張Hの充満忠実性を直接返す。全λ-small余極限閉包としての像の判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`

:::

:::lemma_ "kerodon_9_5_5_19"
Kerodon Lemma 9.5.5.19（[Tag 06P2](https://kerodon.net/tag/06P2)）。対応表の状態：なし。

κ-filtered生成によるInd比較は指定λ-small全余極限生成と数値λの同じ完備化に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`

:::

:::proposition "kerodon_9_5_5_21"
Kerodon Proposition 9.5.5.21（[Tag 06P4](https://kerodon.net/tag/06P4)）。対応表の状態：一部。

κ-presentableのpresentable成分から同じCの局所小性と余完備性(a)(b)が直接得られる。小κ-compact族による全小余極限生成を含む全iffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable.hasSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating`

:::

:::corollary "kerodon_9_5_5_22"
Kerodon Corollary 9.5.5.22（[Tag 06UT](https://kerodon.net/tag/06UT)）。対応表の状態：一部。

κ≤λをIsCardinalChangeBound κ λへ強めると同じCのκ-accessibilityをλ-accessibilityへ移せる。元のpresentabilityと論理積にして同じCのλ-presentabilityを得る。任意の基数比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_accessibilityCardinalAbove`

:::

# 9.5.6 Bousfield Localization

%%%
number := false
tag := "kerodon-9-5-6"
%%%

Kerodon [Tag 06UU](https://kerodon.net/tag/06UU)

:::definition "kerodon_9_5_6_1"
Kerodon Definition 9.5.6.1（[Tag 06UV](https://kerodon.net/tag/06UV)）。対応表の状態：一部。

FをrepleteなReflectiveSubcategoryのreflectorに限り、始域・その部分圏のIsPresentableを課すと、その構造の随伴と充満包含は原文の同じFのBousfield条件を直接表す。任意のFによる定義全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable`

:::

:::proposition "kerodon_9_5_6_2"
Kerodon Proposition 9.5.6.2（[Tag 06UW](https://kerodon.net/tag/06UW)）。対応表の状態：一部。

同じ反射のreflectorには随伴による余極限保存とisLocalizationがあり、原文のBousfield⇒(1)(2)を直接返す。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_preservesSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization`

:::

:::definition "kerodon_9_5_6_9"
Kerodon Definition 9.5.6.9（[Tag 06V3](https://kerodon.net/tag/06V3)）。対応表の状態：一部。

IsReflectiveSubcategoryは同じ部分圏に要求する定義のreflective成分を直接与える。accessibly embedded成分と併せた全定義はこの引用だけでは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_reflection`

:::

:::proposition "kerodon_9_5_6_15"
Kerodon Proposition 9.5.6.15（[Tag 06V9](https://kerodon.net/tag/06V9)）。対応表の状態：一部。

部分圏をrepleteにも強めればreflective\_mem\_limitConeは同じ部分圏の小極限閉性という右辺一成分を直接返す。accessibilityと逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`

:::

:::corollary "kerodon_9_5_6_19"
Kerodon Corollary 9.5.6.19（[Tag 06VD](https://kerodon.net/tag/06VD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の集合に関する局所対象の presentability と accessible な引戻しの結果はある。連続 accessible な G の逆像が反射部分圏になるための左随伴まで組み立てる型は未確認。

:::

:::corollary "kerodon_9_5_6_20"
Kerodon Corollary 9.5.6.20（[Tag 06VE](https://kerodon.net/tag/06VE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の presentability と随伴間の変換の同値はある。任意の二つの連続 accessible な関手間の α が可逆な頂点の全部分圏が Bousfield 局所化となる結果は未確認。

:::

:::corollary "kerodon_9_5_6_21"
Kerodon Corollary 9.5.6.21（[Tag 06VF](https://kerodon.net/tag/06VF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一組の辺に対する局所対象と生成辺の増加に対する反単調性はある。任意の小族の反射部分圏の共通部分を、共通の生成辺集合で表して局所化する型は未確認。

:::

# 9.5.7 Existence of Bousfield Localizations

%%%
number := false
tag := "kerodon-9-5-7"
%%%

Kerodon [Tag 06VG](https://kerodon.net/tag/06VG)

:::theorem "kerodon_9_5_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject")
Kerodon Theorem 9.5.7.1（[Tag 06VH](https://kerodon.net/tag/06VH)）。対応表の状態：本体にある。

仮定：presentable な quasicategory C と小さい添字型で与えた辺の族。集合 W はその像で表せる（Kerodon と一致）。結論：W-local 頂点の部分∞圏が反射部分圏で presentable（原文の Bousfield 局所化と一致）。

:::

:::proposition "kerodon_9_5_7_2"
Kerodon Proposition 9.5.7.2（[Tag 06VJ](https://kerodon.net/tag/06VJ)）。対応表の状態：なし。

IsLocalizationの前合成は全関手準圏の型。原文の両側のcocontinuous全部分圏へ同じ射を制限した充満忠実性・像との比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_generatedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization`

:::

:::proposition "kerodon_9_5_7_5"
Kerodon Proposition 9.5.7.5（[Tag 06VL](https://kerodon.net/tag/06VL)）。対応表の状態：一部。

小さい同じWからbousfield\_isReflectiveSubcategoryとbousfieldLocalObjects\_isPresentableによりW-local部分圏の反射性とaccessibilityを得る。包含のaccessibilityは別入力なので右⇒左の全体ではなく反射性・部分圏のaccessibilityの成分。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences`

:::

:::corollary "kerodon_9_5_7_6"
Kerodon Corollary 9.5.7.6（[Tag 06VM](https://kerodon.net/tag/06VM)）。対応表の状態：なし。

IsLocalizationの全関手圏への前合成の充満忠実性は、原文のPrLの指定写像空間の(-1)-truncated比較と直接同じ型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace`

:::

:::corollary "kerodon_9_5_7_8"
Kerodon Corollary 9.5.7.8（[Tag 06VP](https://kerodon.net/tag/06VP)）。対応表の状態：一部。

W-local部分圏のpresentability、presheaf\_isPresentableと同値不変性から、原文のそのような小K,Wの表示が存在⇒Cがpresentableを直接得る。一般反射を小Wで表す逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_presheafReflection`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable`

:::

:::proposition "kerodon_9_5_7_10"
Kerodon Proposition 9.5.7.10（[Tag 06VR](https://kerodon.net/tag/06VR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定の生成辺による反射局所化と、辺を反転する関手の延長はある。任意の余連続 H に対し、延長が保存的かつ余連続である形の分解をまとめる型は未確認。

:::

