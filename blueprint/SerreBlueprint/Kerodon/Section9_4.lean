import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AdjunctionHomPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeCardinalAccessibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactPullback
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IndComplete
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PullbackFilteredColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CompactGeneration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CompactIndCompletion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndAccessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactModelGenerators
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ObjectCompactCardinals
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Presentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCompactObjects
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectiveAccessibility
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "9.4 Compact Generation and Accessibility" =>
%%%
number := false
tag := "kerodon-9-4"
%%%

Kerodon の 9.4 節（[Tag 06GT](https://kerodon.net/tag/06GT)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_9_4_0_1" (lean := "CategoryTheory.IsCardinalAccessibleCategory, CategoryTheory.IsAccessibleCategory")
Kerodon Definition 9.4.0.1（[Tag 06GU](https://kerodon.net/tag/06GU)）。対応表の状態：Mathlib にある。

仮定：通常圏 C と小さい宇宙での正則 κ（Kerodon と一致）。結論：IsCardinalAccessibleCategory は小 κ-filtered 余極限と κ-presentable 生成を要求し、κ-presentable 全体の本質小性も得られる。IsAccessibleCategory はそのような κ の存在（原文と一致）。

:::

# 9.4.1 Compactly Generated ∞-Categories

%%%
number := false
tag := "kerodon-9-4-1"
%%%

Kerodon [Tag 0673](https://kerodon.net/tag/0673)

:::definition "kerodon_9_4_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating")
Kerodon Definition 9.4.1.1（[Tag 0674](https://kerodon.net/tag/0674)）。対応表の状態：一部。

IsKappaAccessibleとIsKappaCompactGeneratingのfieldsは、κ=ℵ0で小さいcompact generator圏の存在も仮定し、同じCのκ-filtered余極限存在と各対象のcompact図式による表示を直接与える。原文の生成族全体に小ささを要求しない定義全体は含まない。

:::

:::definition "kerodon_9_4_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating")
Kerodon Definition 9.4.1.5（[Tag 0676](https://kerodon.net/tag/0676)）。対応表の状態：一部。

IsKappaAccessibleとIsKappaCompactGeneratingのfieldsは、同じκで小さいcompact generator圏の存在も仮定し、同じCのκ-filtered余極限存在と各対象のcompact図式による表示を直接与える。原文の生成族全体に小ささを要求しない定義全体は含まない。

:::

:::definition "kerodon_9_4_1_7"
Kerodon Variant 9.4.1.7（[Tag 0678](https://kerodon.net/tag/0678)）。対応表の状態：なし。

B6型照合：(κ,λ) 版はなし。λ=∞ かつ小さい生成圏の場合だけ。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible`

:::

:::proposition "kerodon_9_4_1_11"
Kerodon Proposition 9.4.1.11（[Tag 067B](https://kerodon.net/tag/067B)）。対応表の状態：なし。

B6型照合：κ-accessible ⇔ ある小さい A で Ind\_κ(A) ≃ C。λ=∞（Ind\_κ）の場合だけ、C' 小。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible.exists_indRepresentation`

:::

:::corollary "kerodon_9_4_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible.exists_indRepresentation")
Kerodon Corollary 9.4.1.13（[Tag 067C](https://kerodon.net/tag/067C)）。対応表の状態：一部。

Cが同じκでaccessibleという小さい生成圏の仮定も加えると、isKappaAccessible\_iff\_indEquivalenceが原文(2)の同じCのInd表示を直接返す。任意の大きさのcompact生成と(3)の全比較は含まない。

:::

:::corollary "kerodon_9_4_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_indEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence")
Kerodon Corollary 9.4.1.14（[Tag 067D](https://kerodon.net/tag/067D)）。対応表の状態：一部。

Cが同じκ=ℵ0でaccessibleという小さい生成圏の仮定も加えると、isKappaAccessible\_iff\_indEquivalenceが原文(2)の同じCのInd表示を直接返す。任意の大きさのcompact生成と(3)の全比較は含まない。

:::

:::corollary "kerodon_9_4_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaAccessibleFunctor_of_indHomTests_native")
Kerodon Corollary 9.4.1.17（[Tag 06H0](https://kerodon.net/tag/06H0)）。対応表の状態：一部。

標的Cを小準圏Aの標準Indκ(A)、数値λ制限のない全小κ-filtered形状に限ると、isKappaAccessibleFunctor\_of\_indHomTests\_nativeのμ=κへ全compact対象のテストを特殊化して同じGの保存性を得る。任意二濃度の場合は含まない。

:::

:::proposition "kerodon_9_4_1_18"
Kerodon Proposition 9.4.1.18（[Tag 067K](https://kerodon.net/tag/067K)）。対応表の状態：なし。

B6型照合：全単射としての主張はない。冪等完備 C ≃ Ind\_κ(C)\^κ と accessible ⇔ Ind\_κ 同値の二つの半分（C 小、λ=∞（Ind\_κ）の場合だけ）。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence`

:::

:::corollary "kerodon_9_4_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence")
Kerodon Corollary 9.4.1.19（[Tag 067L](https://kerodon.net/tag/067L)）。対応表の状態：一部。

compactGenerationEquivalenceは、冪等完備な小さいCをIndκへ送りcompact対象の全部分圏へ戻したとき同じCを回収する同値を直接与える。全同値類への全単射の構成全体は含まない。

:::

:::corollary "kerodon_9_4_1_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndOmegaEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_indEquivalence")
Kerodon Corollary 9.4.1.20（[Tag 067M](https://kerodon.net/tag/067M)）。対応表の状態：一部。

compactGenerationEquivalenceのκ=ℵ0は、冪等完備な小さいCをIndκへ送りcompact対象の全部分圏へ戻したとき同じCを回収する同値を直接与える。全同値類への全単射の構成全体は含まない。

:::

:::proposition "kerodon_9_4_1_21"
Kerodon Proposition 9.4.1.21（[Tag 06H1](https://kerodon.net/tag/06H1)）。対応表の状態：なし。

B6型照合：κ-accessible な Indκ(C) の構成と Yoneda の κ-compact 生成性。原文の三基数の関係と、C が冪等完備な場合の逆向きは未確認。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`

:::

:::corollary "kerodon_9_4_1_22"
Kerodon Corollary 9.4.1.22（[Tag 06H2](https://kerodon.net/tag/06H2)）。対応表の状態：なし。

B6型照合：κ ◁ μ で κ-accessible ⇒ μ-accessible の向きに関連するのみ。(κ,μ) の同値の判定はなし。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indInfinity_isMuAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound`

:::

# 9.4.2 Compact Functors

%%%
number := false
tag := "kerodon-9-4-2"
%%%

Kerodon [Tag 06H3](https://kerodon.net/tag/06H3)

:::definition "kerodon_9_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_hom_preservesKappaFilteredColimits_iff")
Kerodon Definition 9.4.2.1（[Tag 06H4](https://kerodon.net/tag/06H4)）。対応表の状態：一部。

PreservesKappaFilteredColimitsのκ=ℵ0は同じFのfinitaryという定義の一成分を直接与える。compact対象を全てcompactへ送る一般条件とその全部分圏の構成は含まない。

:::

:::definition "kerodon_9_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image")
Kerodon Variant 9.4.2.2（[Tag 06H5](https://kerodon.net/tag/06H5)）。対応表の状態：一部。

PreservesKappaFilteredColimitsは同じFのfinitaryという定義の一成分を直接与える。compact対象を全てcompactへ送る一般条件とその全部分圏の構成は含まない。

:::

:::definition "kerodon_9_4_2_4"
Kerodon Variant 9.4.2.4（[Tag 06H7](https://kerodon.net/tag/06H7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の関手の κ-accessibility は小 κ-filtered 余極限の保存であり、PrL は小余極限の保存を課す。κ≤λ における finitary 条件と compact 対象保存の両方を課した全部分圏は確認できない。

:::

:::definition "kerodon_9_4_2_15"
Kerodon Notation 9.4.2.15（[Tag 06HJ](https://kerodon.net/tag/06HJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：presentable 圏を集める構成と単独の κ-accessibility はある。原文の (κ,λ)-compactly generated 圏を対象とし、compact 対象も保つ関手を射にする QC の部分圏は未確認。

:::

:::proposition "kerodon_9_4_2_18"
Kerodon Proposition 9.4.2.18（[Tag 06HM](https://kerodon.net/tag/06HM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小 κ-filtered な半順序の κ-compact 図式から選んだ余極限頂点が μ-compact となる部分はある。三濃度での関手の compact 性、制限上の (κ,λ)-compact 性、余域生成を仮定した逆向きは見つからない。

:::

:::corollary "kerodon_9_4_2_19"
Kerodon Corollary 9.4.2.19（[Tag 06HN](https://kerodon.net/tag/06HN)）。対応表の状態：なし。

B6型照合：一つの κ について小 κ-filtered 余極限を保つ関手の Ind 制限同値はある。冪等完備な D に対し、双方を λ から μ へ延長し、compact 対象も保つ関手に制限する同値は確認できない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

# 9.4.3 Compact Generation of Reflective Localizations

%%%
number := false
tag := "kerodon-9-4-3"
%%%

Kerodon [Tag 06YM](https://kerodon.net/tag/06YM)

:::proposition "kerodon_9_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveSubcategory_isKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_reflection")
Kerodon Proposition 9.4.3.1（[Tag 06YN](https://kerodon.net/tag/06YN)）。対応表の状態：一部。

Cをℵ0-accessibleかつ全小余完備、部分圏をrepleteとし、その包含のℵ0-filtered余極限保存を与えるとreflectiveSubcategory\_isKappaAccessibleは同じ部分圏のℵ0-accessibility、従ってcompact生成を返す。一般のcompact生成だけの場合は含まない。

:::

:::proposition "kerodon_9_4_3_4"
Kerodon Proposition 9.4.3.4（[Tag 06YR](https://kerodon.net/tag/06YR)）。対応表の状態：なし。

B6型照合：(κ,λ)-compactly generated 版はなし。κ-accessible の反射部分圏の場合のみ。「(κ,λ)-compactly generated」の述語は SerrePositivity にない（κ-accessible のみ）。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveSubcategory_isKappaAccessible`

:::

:::proposition "kerodon_9_4_3_5"
Kerodon Proposition 9.4.3.5（[Tag 06YS](https://kerodon.net/tag/06YS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間と同値である述語と、有限単体集合の Kan 置換を有限コードで表す宣言はある。任意の n に対する空間の n 切断、および有限な K からの (n+1)-連結な射との同値は確認できない。

:::

:::definition "kerodon_9_4_3_6"
Kerodon Notation 9.4.3.6（[Tag 06YT](https://kerodon.net/tag/06YT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間の充満忠実な埋め込みと全空間の有限模型の生成圏を確認した。n 切断と本質的有限性の両方を課す S\^\{≤n\}\_fin という全部分圏は未確認。

:::

:::proposition "kerodon_9_4_3_9"
Kerodon Proposition 9.4.3.9（[Tag 06YW](https://kerodon.net/tag/06YW)）。対応表の状態：なし。

全Spaceでの有限generatorのcompact性は、原文のn-truncated部分圏内のcompact性やn-truncationとの比較を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex_isCompact`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.exists_finiteSpaceGeneratorIso`

:::

:::definition "kerodon_9_4_3_10"
Kerodon Variant 9.4.3.10（[Tag 06YX](https://kerodon.net/tag/06YX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー圏と有限単体集合のコードは確認した。mapping space の局所 (n−1) 切断と K→C の (n+1)-圏論的連結性をつなぐ原文の二条件は未確認。

:::

:::definition "kerodon_9_4_3_12"
Kerodon Notation 9.4.3.12（[Tag 06YZ](https://kerodon.net/tag/06YZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限な単体集合のコードと、離散空間の述語を確認した。局所 (n−1) 切断で有限模型から来る準圏を選ぶ QC\^\{≤n\}\_fin の宣言は未確認。

:::

:::proposition "kerodon_9_4_3_13"
Kerodon Proposition 9.4.3.13（[Tag 06Z0](https://kerodon.net/tag/06Z0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の離散性と離散空間の充満忠実な表示はある。Kan 複体を準圏と見たとき、空間としての有限模型条件と局所切断による圏としての有限模型条件が一致する定理は未確認。

:::

:::proposition "kerodon_9_4_3_14"
Kerodon Proposition 9.4.3.14（[Tag 06Z1](https://kerodon.net/tag/06Z1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限余極限のある一般の準圏で κ-コンパクト対象が有限余極限で閉じる結果は確認した。QC\^\{≤n\} における有限模型の部分圏を同定する段がないため、原文の閉性はこの型から確認できない。

:::

:::corollary "kerodon_9_4_3_15"
Kerodon Corollary 9.4.3.15（[Tag 06Z2](https://kerodon.net/tag/06Z2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般のコンパクト対象の閉性と空間側の有限模型はある。局所切断された圏における Δ¹ を含む最小の有限余極限閉部分圏の同定は未確認。

:::

:::corollary "kerodon_9_4_3_16"
Kerodon Corollary 9.4.3.16（[Tag 06Z3](https://kerodon.net/tag/06Z3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間のコンパクト生成と一般のコンパクト対象の有限余極限閉性を確認した。切断空間における有限模型の部分圏と、その圏で計算した有限余極限の閉性は未確認。

:::

:::corollary "kerodon_9_4_3_17"
Kerodon Corollary 9.4.3.17（[Tag 06Z4](https://kerodon.net/tag/06Z4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の空間の生成族は全ての有限単体集合の Kan 置換。原文が特定する Δ⁰ 一つからの有限余極限閉包を、S\^\{≤n\}\_fin と同定する結論は確認できない。

:::

:::corollary "kerodon_9_4_3_18"
Kerodon Corollary 9.4.3.18（[Tag 06Z5](https://kerodon.net/tag/06Z5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の準圏の冪等完備化は作れる。原文の二つの有限切断部分圏がそのまま冪等完備であることや、有限模型が retract を取っても存在することは未確認。

:::

:::definition "kerodon_9_4_3_19"
Kerodon Variant 9.4.3.19（[Tag 06Z6](https://kerodon.net/tag/06Z6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合を定義域にした内部 Hom のアクセス可能性は確認した。局所切断圏の圏でのコンパクト性から有限模型を回収する向きも、その逆向きも確認できない。

:::

:::corollary "kerodon_9_4_3_20"
Kerodon Corollary 9.4.3.20（[Tag 06Z7](https://kerodon.net/tag/06Z7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間が有限単体模型で ℵ₀-アクセス可能になる結果はある。原文の n 切断空間および局所切断圏を、それぞれの有限模型の Ind 完備化とする二つの同定は未確認。

:::

:::definition "kerodon_9_4_3_21"
Kerodon Variant 9.4.3.21（[Tag 06Z8](https://kerodon.net/tag/06Z8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間のアクセス可能性と有限単体模型のコードを確認した。κ-小かつ n 切断という制約を持つ空間や準圏を、同じ基数で制限した Ind\_\{ℵ₀\}\^\{κ\} と同定する型は未確認。

:::

# 9.4.4 Compact Generation of Oriented Fiber Products

%%%
number := false
tag := "kerodon-9-4-4"
%%%

Kerodon [Tag 06HP](https://kerodon.net/tag/06HP)

:::proposition "kerodon_9_4_4_1"
Kerodon Proposition 9.4.4.1（[Tag 06NA](https://kerodon.net/tag/06NA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：コンパクトな図式を指定して作る slice 射影と、右ファイブレーションの厳密な filtered 余極限を調べた。任意の右ファイブレーションの全空間への (κ,λ)-compact 生成の移送、および射影による compact 性の両向きは未確認。

:::

:::corollary "kerodon_9_4_4_2"
Kerodon Corollary 9.4.4.2（[Tag 06HU](https://kerodon.net/tag/06HU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：slice の余極限を射影の余極限から得る型と、指定した compact source slice の密度余錐はある。任意の図式上の slice の compact 生成と射影での compact 性判定は確認できない。

:::

:::theorem "kerodon_9_4_4_4" (uses := "kerodon_1_4_0_1, kerodon_3_3_7_4, kerodon_4_3_7_2, kerodon_4_7_3_20, kerodon_4_7_3_23, kerodon_7_1_9_3, kerodon_7_1_9_4, kerodon_7_2_2_3, kerodon_7_4_3_14, kerodon_9_1_5_14, kerodon_9_2_8_3, kerodon_9_3_2_3, kerodon_9_3_2_5, kerodon_9_4_4_15")
Kerodon Theorem 9.4.4.4（[Tag 06HR](https://kerodon.net/tag/06HR)）。対応表の状態：なし。

引用は通常圏のisCardinalAccessibleCategoryについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.Comma.isCardinalAccessibleCategory`、`CategoryTheory.Comma.isCardinalPresentable_iff`

:::

:::corollary "kerodon_9_4_4_6" (uses := "kerodon_1_4_0_1, kerodon_9_4_4_4")
Kerodon Corollary 9.4.4.6（[Tag 06HT](https://kerodon.net/tag/06HT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同時に二脚の濃度別保存と compact 性を仮定した通常の引き戻しの accessibility はある。任意の向き付き引き戻しで、一方の脚だけが compact 対象を保つときの同じ κ での生成と両成分による compact 性判定は見つからない。

:::

:::corollary "kerodon_9_4_4_7"
Kerodon Corollary 9.4.4.7（[Tag 06HW](https://kerodon.net/tag/06HW)）。対応表の状態：なし。

B6型照合：非可算な μ と小余完備性のもとで、小さい図式の各頂点と余錐頂点の μ-compact 性から coslice 内の compact 性を導く型がある。二濃度での coslice の compact 生成と compact 性の逆向きは確認できない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaCompact_smallSourceCosliceVertex`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasSmallKappaFilteredColimits`

:::

:::corollary "kerodon_9_4_4_9"
Kerodon Corollary 9.4.4.9（[Tag 06HY](https://kerodon.net/tag/06HY)）。対応表の状態：なし。

全関手準圏のcompact性の型には追加のend familyが必要で、原文の二濃度compact生成・全頂点判定との比較を持たない。有限posetや小形状というだけでは同じ結論を直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily`

:::

:::corollary "kerodon_9_4_4_12"
Kerodon Corollary 9.4.4.12（[Tag 06J1](https://kerodon.net/tag/06J1)）。対応表の状態：なし。

presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensor_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensorHom_isKappaAccessible`

:::

:::proposition "kerodon_9_4_4_13"
Kerodon Proposition 9.4.4.13（[Tag 06J2](https://kerodon.net/tag/06J2)）。対応表の状態：なし。

presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap_isKappaAccessible`

:::

:::corollary "kerodon_9_4_4_14"
Kerodon Corollary 9.4.4.14（[Tag 06J3](https://kerodon.net/tag/06J3)）。対応表の状態：なし。

presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable`

:::

:::lemma_ "kerodon_9_4_4_15" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 9.4.4.15（[Tag 06J4](https://kerodon.net/tag/06J4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：選んだ部分複体への左ファイブレーションの引き戻しを使う比較と単射像の小ささはある。弱可縮な全空間から、同時に弱可縮かつ λ-small で、制限が左ファイブレーションとなる部分を選ぶ型は見つからない。

:::

# 9.4.5 Compact Generation of Homotopy Fiber Products

%%%
number := false
tag := "kerodon-9-4-5"
%%%

Kerodon [Tag 06J5](https://kerodon.net/tag/06J5)

:::proposition "kerodon_9_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isKappaAccessible_of_relativeCardinals, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects_isPullback")
Kerodon Proposition 9.4.5.2（[Tag 06J7](https://kerodon.net/tag/06J7)）。対応表の状態：一部。

pullback\_isKappaAccessible\_of\_relativeCardinalsでμを原文のκとし、より小さい正則基数とのcardinal change bound、底のμ-accessibility、strict pullbackとequivalence liftingなど追加入力を置くと同じpullbackのμ-accessibilityを直接返す。一般のcategorical pullbackとcompact対象の逆向きは含まない。

:::

:::theorem "kerodon_9_4_5_4"
Kerodon Theorem 9.4.5.4（[Tag 06J9](https://kerodon.net/tag/06J9)）。対応表の状態：なし。

pullback\_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`

:::

:::corollary "kerodon_9_4_5_7"
Kerodon Corollary 9.4.5.7（[Tag 06JC](https://kerodon.net/tag/06JC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の Kan ファイブレーション塔における極限と、二脚の引戻しの accessibility は確認した。κ₀-sequential 余極限を保つ compact な isofibration の塔で、逆極限の compact 生成および各段による判定を得る型は未確認。

:::

:::corollary "kerodon_9_4_5_8"
Kerodon Corollary 9.4.5.8（[Tag 06JD](https://kerodon.net/tag/06JD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引き戻しの accessibility と厳密な単体集合極限の filtered 余極限保存はある。可算 isofibration 塔の準圏極限に同じ κ の compact 生成を与え、各段で compact かどうかで判定する型は見つからない。

:::

:::theorem "kerodon_9_4_5_9" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_22, kerodon_4_9_5_19, kerodon_7_1_4_27, kerodon_7_1_9_1, kerodon_7_1_9_8, kerodon_7_2_2_3, kerodon_9_2_4_3, kerodon_9_2_5_24, kerodon_9_2_8_5, kerodon_9_3_2_5, kerodon_9_3_4_15, kerodon_9_3_7_11")
Kerodon Theorem 9.4.5.9（[Tag 06JE](https://kerodon.net/tag/06JE)）。対応表の状態：なし。

pullback\_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`

:::

:::corollary "kerodon_9_4_5_10" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_21, kerodon_4_5_3_24, kerodon_4_5_3_28, kerodon_4_5_3_29, kerodon_9_4_5_9")
Kerodon Corollary 9.4.5.10（[Tag 06JG](https://kerodon.net/tag/06JG)）。対応表の状態：なし。

pullback\_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`

:::

:::proposition "kerodon_9_4_5_11"
Kerodon Proposition 9.4.5.11（[Tag 06JH](https://kerodon.net/tag/06JH)）。対応表の状態：なし。

pullback\_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor`

:::

# 9.4.6 Compactly Generated Fibrations

%%%
number := false
tag := "kerodon-9-4-6"
%%%

Kerodon [Tag 06JJ](https://kerodon.net/tag/06JJ)

:::definition "kerodon_9_4_6_1"
Kerodon Definition 9.4.6.1（[Tag 06JK](https://kerodon.net/tag/06JK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏に対する生成関手の述語と任意の底変換はある。内ファイブレーションを各標準単体へ引き戻した全空間に、ℵ₀-compact 生成を要求する述語は未確認。

:::

:::definition "kerodon_9_4_6_2"
Kerodon Variant 9.4.6.2（[Tag 06JL](https://kerodon.net/tag/06JL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の κ-accessibility と指定二脚の引き戻しを扱う宣言はある。内ファイブレーションを任意の Δⁿ 上に引き戻して κ-compact 生成を要求する述語は見つからない。

:::

:::definition "kerodon_9_4_6_4"
Kerodon Variant 9.4.6.4（[Tag 06JN](https://kerodon.net/tag/06JN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：濃度変更を使う指定引き戻しの定理はある。引き戻しをすべての Δⁿ 上で取り、その各全空間に (κ,λ)-compact 生成を要求する定義は見つからない。

:::

:::proposition "kerodon_9_4_6_8"
Kerodon Proposition 9.4.6.8（[Tag 06JV](https://kerodon.net/tag/06JV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアンな辺での輸送と二脚の引戻しの accessibility はある。全単体上の compact 生成を、頂点ファイバーと Δ¹ 上の始点包含の finitary 性・compact 保存だけで特徴付ける型は未確認。

:::

:::proposition "kerodon_9_4_6_9"
Kerodon Proposition 9.4.6.9（[Tag 06JU](https://kerodon.net/tag/06JU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の Ind の κ-compact 生成と compact 部分の冪等完備化はある。底上で U を U₀ の相対 Ind とする条件と、U₀ を各ファイバーの compact 対象から選ぶ構成は未確認。

:::

:::corollary "kerodon_9_4_6_10"
Kerodon Corollary 9.4.6.10（[Tag 06JS](https://kerodon.net/tag/06JS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：大域的なカルテシアン・ファイブレーションから反変輸送を作れる。局所的な射に対し、その各輸送の (κ,λ)-finitary 性とファイバーの生成が全単体での生成と同値になる結論は未確認。

:::

:::corollary "kerodon_9_4_6_11"
Kerodon Corollary 9.4.6.11（[Tag 06JT](https://kerodon.net/tag/06JT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：大域的な余カルテシアン射の輸送関手を確認した。局所余カルテシアンな場合に、各輸送の (κ,λ)-compact 性とファイバーの生成を全単体での生成と結ぶ同値は未確認。

:::

:::proposition "kerodon_9_4_6_12"
Kerodon Proposition 9.4.6.12（[Tag 06JW](https://kerodon.net/tag/06JW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の射の切断を相対関手空間で表す構成と、固定標的への関手の点ごとの余極限および条件付き compact 性はある。変動ファイバーでの切断の余完備性、点ごとの compact 性、切断圏の相対 Ind の充満忠実性は未確認。

:::

:::theorem "kerodon_9_4_6_13"
Kerodon Theorem 9.4.6.13（[Tag 06JX](https://kerodon.net/tag/06JX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい生成モデルと一つの圏の Ind 比較を確認した。κ₀-sequential 余極限を使い、切断が compact 部分を経由することを compact 性と同値にし、その切断圏を相対 Ind と同定する定理は未確認。

:::

:::corollary "kerodon_9_4_6_14"
Kerodon Corollary 9.4.6.14（[Tag 06JY](https://kerodon.net/tag/06JY)）。対応表の状態：なし。

全関手準圏のcompact性の型には追加のend familyが必要で、原文の二濃度compact生成・全頂点判定との比較を持たない。有限posetや小形状というだけでは同じ結論を直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily`

:::

:::corollary "kerodon_9_4_6_16"
Kerodon Corollary 9.4.6.16（[Tag 06K0](https://kerodon.net/tag/06K0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定形状の余カルテシアン切断の準圏性と、通常圏の重み付き切断関手の filtered 余極限保存を確認した。コンパクトなファイバーへの因子化と切断の compact 性の同値、さらに相対 Ind 同値は未確認。

:::

:::corollary "kerodon_9_4_6_17"
Kerodon Corollary 9.4.6.17（[Tag 06K1](https://kerodon.net/tag/06K1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引戻しの accessibility と厳密な単体集合極限の交換はある。任意の κ-小図式の QC での極限を同じ二濃度で compact 生成し、各評価で compact 性を特徴付ける型は未確認。

:::

:::corollary "kerodon_9_4_6_20"
Kerodon Corollary 9.4.6.20（[Tag 06K4](https://kerodon.net/tag/06K4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の制限の普遍性と厳密な単体集合極限の交換を確認した。逐次余極限を保存する関手からなる QC 部分圏上で、相対 Ind\_\{κ\}\^\{λ\} が κ-小極限を保存する宣言は未確認。

:::

# 9.4.7 Accessible ∞-Categories

%%%
number := false
tag := "kerodon-9-4-7"
%%%

Kerodon [Tag 06K5](https://kerodon.net/tag/06K5)

:::definition "kerodon_9_4_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence")
Kerodon Definition 9.4.7.1（[Tag 06K6](https://kerodon.net/tag/06K6)）。対応表の状態：本体にある。

仮定：Quasicategory C と小さい正則 κ（Kerodon と一致）。結論：IsKappaAccessible κ C と小さい A からの IndInfinity κ A との圏同値の存在を比較（原文の Ind 完備化の定義と一致）。

:::

:::proposition "kerodon_9_4_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating")
Kerodon Proposition 9.4.7.2（[Tag 06K7](https://kerodon.net/tag/06K7)）。対応表の状態：一部。

isKappaAccessible\_iff\_indEquivalenceは小さいAからの同じCのIndκ表示という条件(1)の実現を直接与える。essentially smallへの拡張とcompact対象全体の小性を含む全同値は含まない。

:::

:::corollary "kerodon_9_4_7_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndYoneda_isIdempotentCompletion, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_isIdempotentComplete")
Kerodon Corollary 9.4.7.3（[Tag 06K8](https://kerodon.net/tag/06K8)）。対応表の状態：一部。

indInfinity\_isKappaAccessibleは同じ小さい冪等完備CをIndκへ送った圏のκ-accessibilityを直接返す。全同値類の単射・全射の両方はこの引用だけでは含まない。

:::

:::proposition "kerodon_9_4_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indInfinity_isMuAccessible")
Kerodon Proposition 9.4.7.5（[Tag 06KA](https://kerodon.net/tag/06KA)）。対応表の状態：一部。

κ⊴λを指数によるIsCardinalChangeBound κ λへ強めるとof\_cardinalChangeBoundは同じCのλ-accessibilityを直接返す。任意の非厳密sharply条件の場合は含まない。

:::

:::corollary "kerodon_9_4_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound")
Kerodon Corollary 9.4.7.6（[Tag 06KB](https://kerodon.net/tag/06KB)）。対応表の状態：一部。

ℵ0\<κを満たす正則κについてIsCardinalChangeBound ℵ0 κも入力すると、of\_cardinalChangeBoundは同じℵ0-accessibleなCのκ-accessibilityを直接返す。正則性だけからこの追加入力を得たとはしない。

:::

:::corollary "kerodon_9_4_7_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_compactCardinal")
Kerodon Corollary 9.4.7.7（[Tag 06KC](https://kerodon.net/tag/06KC)）。対応表の状態：一部。

IsKappaAccessibleのκ-filtered余極限存在とfiltered性の基数単調性により、同じCの全小λ-filtered余極限存在という前半を直接得る。λ-compact対象全体の小性は含まない。

:::

:::definition "kerodon_9_4_7_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible")
Kerodon Definition 9.4.7.10（[Tag 06KF](https://kerodon.net/tag/06KF)）。対応表の状態：本体にある。

仮定：Quasicategory C（Kerodon と一致）。結論：IsAccessible C は小さい κ に対する IsKappaAccessible κ C の存在で、正則性はその述語に含まれる（原文と一致）。

:::

:::proposition "kerodon_9_4_7_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessible.exists_larger")
Kerodon Proposition 9.4.7.15（[Tag 06KM](https://kerodon.net/tag/06KM)）。対応表の状態：本体にある。

仮定：Quasicategory C と IsAccessible C（Kerodon と一致）。結論：任意の小さい σ を上回る μ で IsKappaAccessible μ C。μ の正則性はこの述語から得られる（原文の任意に大きい小正則基数と一致）。

:::

:::definition "kerodon_9_4_7_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_accessibilityCardinal")
Kerodon Variant 9.4.7.17（[Tag 06KP](https://kerodon.net/tag/06KP)）。対応表の状態：本体にある。

仮定：小さい添字型 ι 上の quasicategory の族と各 IsAccessible（Kerodon と一致）。結論：任意の σ を上回る共通の正則 μ で全ての Cᵢ が IsKappaAccessible μ（原文と一致）。

:::

:::corollary "kerodon_9_4_7_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable")
Kerodon Corollary 9.4.7.18（[Tag 06KQ](https://kerodon.net/tag/06KQ)）。対応表の状態：一部。

各Ciをpresentableにも強めるとpiSSet\_isPresentableの同じ小積はpresentable、従ってaccessibleである。単にaccessibleな因子の場合は含まない。

:::

:::corollary "kerodon_9_4_7_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible.isAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.compactModel_isKappaCompactGenerating")
Kerodon Corollary 9.4.7.19（[Tag 06KR](https://kerodon.net/tag/06KR)）。対応表の状態：一部。

IsKappaAccessibleの定義とisAccessibleから、同じCのκ-accessible⇒accessibleという右辺一成分を直接得る。compact生成を併せた全右辺と逆向きは含まない。

:::

:::proposition "kerodon_9_4_7_20"
Kerodon Proposition 9.4.7.20（[Tag 06KS](https://kerodon.net/tag/06KS)）。対応表の状態：なし。

Indκ(A)がaccessibleかつ冪等完備という型は、原文の本質的小さい同じC自体のiffではない。compact部分圏をwhole Indと同一視しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndYoneda_isIdempotentCompletion`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_isIdempotentComplete`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible`

:::

:::corollary "kerodon_9_4_7_21"
Kerodon Corollary 9.4.7.21（[Tag 06NB](https://kerodon.net/tag/06NB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の κ-filtered 性を nerve に移す型はある。大きな半順序 Q も許して N(Q) の accessibility と Q の小ささを結ぶ iff は見つからない。

:::

:::lemma_ "kerodon_9_4_7_22"
Kerodon Lemma 9.4.7.22（[Tag 06KT](https://kerodon.net/tag/06KT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の集合の余極限における成分からの代表元と、集合を小部分集合の余極限で書く結果を調べた。λ-directed 性を使い、各項が κ 未満なら余極限全体も κ 未満とする濃度評価は未確認。

:::

:::lemma_ "kerodon_9_4_7_23"
Kerodon Lemma 9.4.7.23（[Tag 06KU](https://kerodon.net/tag/06KU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小空間の余極限を取る関手と、κ-small な始域から余極限への写像の因数分解はある。λ-filtered 図式の頂点に課したより小さい本質的 κ-small 性が余極限で保たれる型は見つからない。

:::

:::proposition "kerodon_9_4_7_24"
Kerodon Proposition 9.4.7.24（[Tag 06KV](https://kerodon.net/tag/06KV)）。対応表の状態：なし。

compactIndYonedaはInd内のcompact対象の部分圏への射であり、原文のwhole Indλμへの同じhではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndYoneda_isIdempotentCompletion`

:::

:::corollary "kerodon_9_4_7_25"
Kerodon Corollary 9.4.7.25（[Tag 06KW](https://kerodon.net/tag/06KW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定された図式の retract に余極限を移す補題と Ind の小 κ-filtered 余極限存在はある。本質的 λ-small・局所 κ-small な任意の冪等完備 C の λ-filtered 余極限の存在と、任意の関手による保存は見つからない。

:::

# 9.4.8 Accessible Functors

%%%
number := false
tag := "kerodon-9-4-8"
%%%

Kerodon [Tag 06KX](https://kerodon.net/tag/06KX)

:::definition "kerodon_9_4_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor")
Kerodon Definition 9.4.8.1（[Tag 06KY](https://kerodon.net/tag/06KY)）。対応表の状態：本体にある。

仮定：写像 F:C→D。定義は C,D の accessible 性を引数に要求しない（Lean が弱い）。結論：小さい正則 κ が存在して F が小 κ-filtered 余極限を保存する（原文と一致）。

:::

:::definition "kerodon_9_4_8_8"
Kerodon Definition 9.4.8.8（[Tag 06U5](https://kerodon.net/tag/06U5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：圏と関手それぞれの accessibility、および一つの具体的な部分圏の頂点同型に関する述語はある。replete 性、部分圏の accessibility、包含の accessibility を任意の部分圏について束ねる定義は未確認。

:::

:::proposition "kerodon_9_4_8_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.reflectiveImage_isKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveSubcategory_isKappaAccessible")
Kerodon Proposition 9.4.8.9（[Tag 06U6](https://kerodon.net/tag/06U6)）。対応表の状態：一部。

Cを全小余完備にも強め、同じreplete反射部分圏の包含がある固定κのfiltered余極限を保存するとreflectiveSubcategory\_isKappaAccessibleはその部分圏のκ-accessibilityを返す。原文(4)⇒(2)のこの場合に一致する。

:::

:::definition "kerodon_9_4_8_11"
Kerodon Notation 9.4.8.11（[Tag 06L5](https://kerodon.net/tag/06L5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：対象を presentable に、射を小余極限保存または accessible な小極限保存の条件で絞った構成と、単独の accessible 関手の述語はある。固定された強到達不能濃度で全 accessible 準圏と全 accessible 関手を集めた QC\^Acc の構成は見つからない。

:::

:::proposition "kerodon_9_4_8_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessible.exists_common_compactCardinal, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_accessibilityCardinal")
Kerodon Proposition 9.4.8.12（[Tag 06L6](https://kerodon.net/tag/06L6)）。対応表の状態：一部。

exists\_common\_accessibilityCardinalを同じ二圏へ適用すると、同じ共通λでのaccessibilityを直接返す。Fiが全λ-compact対象を保存する成分は含まない。

:::

:::definition "kerodon_9_4_8_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_accessibilityCardinal") (uses := "kerodon_1_4_0_1")
Kerodon Variant 9.4.8.15（[Tag 06L9](https://kerodon.net/tag/06L9)）。対応表の状態：一部。

exists\_common\_accessibilityCardinalを同じ二圏の小さい全族へ適用すると、同じ共通λでのaccessibilityを直接返す。Fiが全λ-compact対象を保存する成分は含まない。

:::

:::proposition "kerodon_9_4_8_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaAccessibleFunctor_of_indHomTests_native")
Kerodon Proposition 9.4.8.17（[Tag 06LB](https://kerodon.net/tag/06LB)）。対応表の状態：一部。

標的を小準圏AのIndκ、全表現可能Homテストが共通の正則μでfiltered余極限を保存することも追加すると、isKappaAccessibleFunctor\_of\_indHomTests\_nativeは同じFのμ-accessibilityを返す。対象ごとに異なる基数しかない場合は含まない。

:::

:::corollary "kerodon_9_4_8_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isAccessibleFunctor")
Kerodon Corollary 9.4.8.18（[Tag 06LC](https://kerodon.net/tag/06LC)）。対応表の状態：本体にある。

仮定：C と D は accessible な準圏で、L ⊣ R を与える（Kerodon と一致）。結論：右随伴の accessibility を直接得て、左随伴は小余極限保存とその accessibility への変換で得る（一致）。

:::

# 9.4.9 Stability Properties of Accessible ∞-Categories

%%%
number := false
tag := "kerodon-9-4-9"
%%%

Kerodon [Tag 06LD](https://kerodon.net/tag/06LD)

:::proposition "kerodon_9_4_9_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorPostcomp_isKappaAccessible")
Kerodon Proposition 9.4.9.1（[Tag 06LE](https://kerodon.net/tag/06LE)）。対応表の状態：一部。

Cをpresentable、Kを小準圏にも強めるとfunctor\_isPresentableは同じFun(K,C)のpresentability、従ってaccessibilityを直接返す。任意KとaccessibleだけのCは含まない。

:::

:::proposition "kerodon_9_4_9_4" (uses := "kerodon_1_4_0_1, kerodon_4_9_5_17, kerodon_9_4_4_6, kerodon_9_4_8_15")
Kerodon Proposition 9.4.9.4（[Tag 06LG](https://kerodon.net/tag/06LG)）。対応表の状態：なし。

通常圏Commaのaccessible性と∞圏Arrowのpresentabilityは、原文の指定二関手のoriented fiber productと同じ対象への比較を含まない。

宣言：`CategoryTheory.Comma.isAccessibleCategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.arrow_isPresentable`

:::

:::corollary "kerodon_9_4_9_6"
Kerodon Corollary 9.4.9.6（[Tag 06LJ](https://kerodon.net/tag/06LJ)）。対応表の状態：なし。

通常圏のOver/StructuredArrowのaccessible性は、原文の∞圏の指定slice/cosliceへのnerve比較を含まない。

宣言：`CategoryTheory.Over.instIsAccessibleCategory`、`CategoryTheory.Under.instIsAccessibleCategory`

:::

:::proposition "kerodon_9_4_9_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible") (uses := "kerodon_1_4_0_1, kerodon_4_9_5_18, kerodon_9_4_5_10, kerodon_9_4_8_15")
Kerodon Proposition 9.4.9.9（[Tag 06LM](https://kerodon.net/tag/06LM)）。対応表の状態：一部。

一方の脚pがequivalence liftingであり、homotopy fiber productを同じstrict pullback模型で与えるとpullback\_isAccessibleが同じ全空間のaccessibilityを直接返す。任意に指定された模型への輸送は含まない。

:::

:::corollary "kerodon_9_4_9_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible")
Kerodon Corollary 9.4.9.11（[Tag 06LP](https://kerodon.net/tag/06LP)）。対応表の状態：一部。

片脚equivalence liftingのstrict pullback模型ではpullback\_isAccessibleと射影のκ-accessibilityから同じ全空間と二射影のaccessibilityを得る。任意の指定categorical pullbackへの比較とTのiffは含まない。

:::

:::corollary "kerodon_9_4_9_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor")
Kerodon Corollary 9.4.9.12（[Tag 06U9](https://kerodon.net/tag/06U9)）。対応表の状態：一部。

逆像をstrict pullbackで取り、Fにequivalence liftingを追加するとpullbackのaccessible性と射影の保存性は同じ逆像部分のaccessibly embedded条件を直接返す。一般のFは含まない。

:::

:::corollary "kerodon_9_4_9_13"
Kerodon Corollary 9.4.9.13（[Tag 06UB](https://kerodon.net/tag/06UB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片脚に同値持ち上げを課した二つの accessible 関手の引き戻しの accessibility はある。accessibly embedded な任意の小族の共通部分と、元の C への包含が accessibly embedded であることを一緒に与える型は見つからない。

:::

:::corollary "kerodon_9_4_9_14"
Kerodon Corollary 9.4.9.14（[Tag 06UC](https://kerodon.net/tag/06UC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間に限った 0 切断とその充満忠実な表示はある。任意の accessible 準圏で n 切断対象を選ぶ構成と、包含および部分圏そのものの accessibility は未確認。

:::

:::corollary "kerodon_9_4_9_15"
Kerodon Corollary 9.4.9.15（[Tag 06LQ](https://kerodon.net/tag/06LQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引戻しで得る圏の accessibility と、厳密な単体集合の交換定理を確認した。accessible 圏・関手の QC 部分圏の任意の小極限、および QC\_\{≤Ω\} への包含での保存は未確認。

:::

:::definition "kerodon_9_4_9_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SSet.quasicategory_of_innerFibration")
Kerodon Definition 9.4.9.16（[Tag 06LR](https://kerodon.net/tag/06LR)）。対応表の状態：本体にある。

同じinner fibration Uについて∀n, ∀σ:Δ\[n\]⟶C, IsAccessible (pullback σ U)という既存の型の全称量化が原文の定義全体に一致する。引戻しの準圏性は標準単体の準圏性とinner fibrationの底変換から得る。

:::

:::definition "kerodon_9_4_9_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SSet.quasicategory_of_innerFibration")
Kerodon Variant 9.4.9.19（[Tag 06LU](https://kerodon.net/tag/06LU)）。対応表の状態：本体にある。

同じinner fibration Uについて∀n, ∀σ:Δ\[n\]⟶C, IsKappaAccessible κ (pullback σ U)という既存の型の全称量化が原文の定義全体に一致する。引戻しの準圏性は標準単体の準圏性とinner fibrationの底変換から得る。

:::

:::proposition "kerodon_9_4_9_23"
Kerodon Proposition 9.4.9.23（[Tag 06LY](https://kerodon.net/tag/06LY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの κ-accessible 準圏の compact 生成モデルと、小さい compact source slice はある。内ファイブレーション全体での四条件、特に各ファイバーの compact 頂点を集めた制限の本質的小ささとの比較は未確認。

:::

:::corollary "kerodon_9_4_9_25"
Kerodon Corollary 9.4.9.25（[Tag 06M0](https://kerodon.net/tag/06M0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚引戻しの accessibility とカルテシアン辺の輸送を確認した。Δ¹ 上だけの accessibility から任意の Δⁿ 上の accessibility を導く iff は未確認。

:::

:::corollary "kerodon_9_4_9_26"
Kerodon Corollary 9.4.9.26（[Tag 06M1](https://kerodon.net/tag/06M1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：大域的なカルテシアン射の反変輸送と、指定 κ の余極限保存述語はある。局所カルテシアン射で、各輸送の κ-finitary 性と頂点ファイバーの条件が全単体上の κ-accessibility と同値になる型は未確認。

:::

:::corollary "kerodon_9_4_9_27"
Kerodon Corollary 9.4.9.27（[Tag 06M2](https://kerodon.net/tag/06M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：大域的な反変輸送の持ち上げと、二脚の accessible 関手に共通濃度を選ぶ結果はある。任意の局所カルテシアン射について各ファイバーと各輸送の accessibility から全単体上の accessibility を得る比較は未確認。

:::

:::corollary "kerodon_9_4_9_28"
Kerodon Corollary 9.4.9.28（[Tag 06M3](https://kerodon.net/tag/06M3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン辺の共変輸送、compact 生成、および余極限保存は個別にある。局所余カルテシアン射における、輸送の κ-compact 性とファイバーの κ-accessibility による全単体の判定は未確認。

:::

:::corollary "kerodon_9_4_9_29"
Kerodon Corollary 9.4.9.29（[Tag 06M4](https://kerodon.net/tag/06M4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：共変の辺輸送とそのホモトピー圏での計算を確認した。各ファイバーと各輸送が濃度を固定せず accessible であることと、全単体上の accessibility の iff は未確認。

:::

:::proposition "kerodon_9_4_9_32"
Kerodon Proposition 9.4.9.32（[Tag 06M7](https://kerodon.net/tag/06M7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対関手空間と通常圏での重み付き切断関手の余極限保存はある。小さい底の上の内ファイブレーションに逐次余完備性を課して、全切断圏の λ-accessibility を得る型は未確認。

:::

:::corollary "kerodon_9_4_9_33"
Kerodon Corollary 9.4.9.33（[Tag 06M8](https://kerodon.net/tag/06M8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：切断の相対関手空間、二脚引戻しの accessibility、左ファイブレーションの切断比較を確認した。任意の小さい底上の edgewise accessible な内ファイブレーションの全切断圏の accessibility は未確認。

:::

