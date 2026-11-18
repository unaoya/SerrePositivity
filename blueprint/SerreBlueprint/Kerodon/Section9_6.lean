import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.ObjectProperty.Local
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.SetTheory.Ordinal.Basic
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.LocalStrongSaturation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.StronglySaturatedClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldSaturation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrowsPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourcePresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalPushoutEquivalences
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalJoinNerveIso

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "9.6 Factorization Systems" =>
%%%
number := false
tag := "kerodon-9-6"
%%%

Kerodon の 9.6 節（[Tag 04KF](https://kerodon.net/tag/04KF)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_9_6_0_1" (lean := "CategoryTheory.HasLiftingProperty, CategoryTheory.MorphismProperty.IsWeakFactorizationSystem")
Kerodon Definition 9.6.0.1（[Tag 06VS](https://kerodon.net/tag/06VS)）。対応表の状態：一部。

通常圏のIsWeakFactorizationSystemのfieldsは同じ左右クラスの因数分解とLLPを与える。原文がさらに要求する持ち上げの一意性は含まない。

:::

:::definition "kerodon_9_6_0_3" (lean := "CategoryTheory.MorphismProperty.IsWeakFactorizationSystem, CategoryTheory.MorphismProperty.IsStableUnderRetracts")
Kerodon Definition 9.6.0.3（[Tag 06VU](https://kerodon.net/tag/06VU)）。対応表の状態：Mathlib にある。

仮定：通常圏 C と二つの MorphismProperty（Kerodon と一致）。結論：IsWeakFactorizationSystem は分解と左右の持ち上げ類との等式で定義。ソースの mk' は分解・retract 閉性・持ち上げの存在からこれを得る（原文の弱分解系と一致）。

:::

# 9.6.1 Digression: Transfinite Composition

%%%
number := false
tag := "kerodon-9-6-1"
%%%

Kerodon [Tag 04KZ](https://kerodon.net/tag/04KZ)

:::definition "kerodon_9_6_1_1"
Kerodon Definition 9.6.1.1（[Tag 04L0](https://kerodon.net/tag/04L0)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib の通常圏では整列形状の極限段の余極限と後続射の W 所属を記録し、始点同型と余錐で合成射を指定する。準圏における指定された閉順序数の神経による構成は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`、`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`、`CategoryTheory.MorphismProperty.transfiniteCompositions`

:::

:::definition "kerodon_9_6_1_3"
Kerodon Variant 9.6.1.3（[Tag 06VX](https://kerodon.net/tag/06VX)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の整列形状を指定する超限合成と、順序数の区間の濃度評価はある。一般の準圏で α\<κ を条件にする超限合成とその閉性の述語は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`、`CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape`

:::

:::definition "kerodon_9_6_1_4" (lean := "CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape, Ordinal.enum, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveIso")
Kerodon Variant 9.6.1.4（[Tag 04L2](https://kerodon.net/tag/04L2)）。対応表の状態：一部。

Ordinal.enumは同じ整列集合Aとその順序型の初切片との順序保存全単射を直接与える。原文のnerveと右joinの同型および超限合成の条件の全比較は含まない。

:::

:::proposition "kerodon_9_6_1_10"
Kerodon Proposition 9.6.1.10（[Tag 04L6](https://kerodon.net/tag/04L6)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では恒等・合成・同型に関する閉性と整列形状の射圏余極限から、超限合成の閉性を得る。原文の非可算正則 κ で制限した準圏 Fun(Δ¹,C) における閉性は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`、`CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape`

:::

:::corollary "kerodon_9_6_1_12"
Kerodon Corollary 9.6.1.12（[Tag 04L8](https://kerodon.net/tag/04L8)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の同型射について超限合成の閉性をインスタンスで得る。準圏では可逆辺の有限合成を調べたが、任意の順序数の連続図式での閉性は未確認。

宣言：`CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition`、`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.isIso`

:::

:::definition "kerodon_9_6_1_13"
Kerodon Definition 9.6.1.13（[Tag 04L9](https://kerodon.net/tag/04L9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の超限合成の下限・上限と、準圏で余極限・二対三を課す別の強飽和閉包を確認した。任意の準圏の κ-小超限合成だけについて最小な閉包を与える宣言は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`

:::

:::proposition "kerodon_9_6_1_16"
Kerodon Proposition 9.6.1.16（[Tag 04LC](https://kerodon.net/tag/04LC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の上限性は既に超限合成で閉じた標的を要求する。別の強飽和閉包には冪等性があるが、恒等射を含む W の κ-小超限合成を再合成して同じ形に平坦化する型は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`

:::

:::lemma_ "kerodon_9_6_1_17"
Kerodon Lemma 9.6.1.17（[Tag 04LD](https://kerodon.net/tag/04LD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：自然数列の spine の内アノダイン性と薄い圏の神経への外延性はある。一般の線形順序の隣接端点条件で定義した K(A,B) の包含の圏同値は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`

:::

:::proposition "kerodon_9_6_1_18"
Kerodon Proposition 9.6.1.18（[Tag 04LE](https://kerodon.net/tag/04LE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：整列形状の順序同型による添字変更と W の単調性はある。非同型の合成射を保ったまま同型な後続射を全て削る別の形状への縮約は確認できない。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`

:::

:::corollary "kerodon_9_6_1_19"
Kerodon Corollary 9.6.1.19（[Tag 04LF](https://kerodon.net/tag/04LF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の全整列形状での合成と準圏での別の最小閉包を確認した。κ-小閉包の元を同型か指定 W の一つの κ-小超限合成に分類する iff は未確認。

宣言：`CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`

:::

# 9.6.2 Weakly Local Objects

%%%
number := false
tag := "kerodon-9-6-2"
%%%

Kerodon [Tag 04LG](https://kerodon.net/tag/04LG)

:::definition "kerodon_9_6_2_1"
Kerodon Definition 9.6.2.1（[Tag 04LH](https://kerodon.net/tag/04LH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の持ち上げで終対象への射を使うと射の延長を表せる。原文は終対象の仮定を置かず、各 w の Hom 写像の全射性を弱い局所性と呼ぶ。既存の通常圏の isLocal は全単射の条件であり、この弱い述語は未確認。

宣言：`CategoryTheory.HasLiftingProperty`

:::

:::definition "kerodon_9_6_2_5"
Kerodon Definition 9.6.2.5（[Tag 04LM](https://kerodon.net/tag/04LM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の既存の述語は前合成の写像空間の同値を課す。原文の各 f に対して三角形を延長できればよい弱い局所性を独立に課す型は未確認。

宣言：`CategoryTheory.MorphismProperty.isLocal`

:::

:::definition "kerodon_9_6_2_12"
Kerodon Variant 9.6.2.12（[Tag 04LV](https://kerodon.net/tag/04LV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：射圏の retract という通常圏側の概念と、準圏で余錐の普遍性を retract へ移す定理はある。弱い局所性と強い局所性を Fun(Δ¹,C) 内の辺の retract で移す型は未確認。

宣言：`CategoryTheory.MorphismProperty.isLocal`

:::

:::proposition "kerodon_9_6_2_13" (lean := "CategoryTheory.MorphismProperty.isLocal, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_pushout_right_of_left, CategoryTheory.MorphismProperty.pushouts_le_llp_rlp")
Kerodon Proposition 9.6.2.13（[Tag 04LW](https://kerodon.net/tag/04LW)）。対応表の状態：一部。

同じwについてXをstrongly localにも強めるとisLocalForHom\_pushout\_right\_of\_leftが同じpushout射w′のstrong localityを返すのでweak localityを得る。weak localityだけの入力ではない。

:::

:::proposition "kerodon_9_6_2_14"
Kerodon Proposition 9.6.2.14（[Tag 04LY](https://kerodon.net/tag/04LY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の写像空間での条件とその pushout 版はある。相対余対角が W に残るという仮定だけで弱い局所性から同値性を導く原文の iff は未確認。

宣言：`CategoryTheory.MorphismProperty.isLocal`

:::

:::proposition "kerodon_9_6_2_16"
Kerodon Proposition 9.6.2.16（[Tag 04M0](https://kerodon.net/tag/04M0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では左持ち上げクラスが超限合成で閉じる。原文の準圏の三角形延長だけで定めた X に対する弱い局所射のクラスが閉じる型は未確認。

宣言：`CategoryTheory.MorphismProperty.isLocal`

:::

# 9.6.3 The Small Object Argument

%%%
number := false
tag := "kerodon-9-6-3"
%%%

Kerodon [Tag 04M7](https://kerodon.net/tag/04M7)

:::definition "kerodon_9_6_3_1"
Kerodon Definition 9.6.3.1（[Tag 04M8](https://kerodon.net/tag/04M8)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏で W の pushout 射を作り、そのクラスの超限合成を取る定義がある。準圏における pushout と κ-小な形状に制限した超限合成での対応は未確認。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`、`CategoryTheory.MorphismProperty.pushouts`、`CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape`

:::

:::theorem "kerodon_9_6_3_3" (lean := "CategoryTheory.MorphismProperty.HasSmallObjectArgument, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_bousfieldLocalReplacement")
Kerodon Theorem 9.6.3.3（[Tag 04MA](https://kerodon.net/tag/04MA)）。対応表の状態：一部。

exists\_bousfieldLocalReplacementは同じ小WとXに対しX→YとW-local（従ってweakly local）なYを直接返す。射がgeneratedEdgesに属する条件はあるが、指定超限pushoutであるという比較は含まない。

:::

:::lemma_ "kerodon_9_6_3_6"
Kerodon Lemma 9.6.3.6（[Tag 04ME](https://kerodon.net/tag/04ME)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余積と pushout を使う超限合成の持ち上げ結論を確認した。準圏の指定図式の余極限による一斉付加を個別 pushout の λ-小超限合成にする型は未確認。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`

:::

:::lemma_ "kerodon_9_6_3_7"
Kerodon Lemma 9.6.3.7（[Tag 04MF](https://kerodon.net/tag/04MF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の後続段と準圏の強飽和局所置換を確認した。hC の λ-小な Hom 類を一斉に付加し、原文の全ての正方形を与える λ-小超限 pushout は未確認。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`

:::

:::lemma_ "kerodon_9_6_3_8"
Kerodon Lemma 9.6.3.8（[Tag 04MG](https://kerodon.net/tag/04MG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の整列連続性と反射の特定の超限列はある。始点と任意の U の各頂点での後続射だけを与えて、準圏内に指定 α までの連続列を作る一般形は未確認。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`

:::

:::proposition "kerodon_9_6_3_9"
Kerodon Proposition 9.6.3.9（[Tag 06VZ](https://kerodon.net/tag/06VZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい辺族の局所対象を作る presentable 版と、通常圏の超限合成の持ち上げ結論はある。λ-余完備性と κ-コンパクトな始域を使い、指定 λ の範囲内で弱い局所対象への射を元の W の超限 pushout にする型は未確認。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`

:::

:::proposition "kerodon_9_6_3_10" (lean := "CategoryTheory.MorphismProperty.HasSmallObjectArgument, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences")
Kerodon Proposition 9.6.3.10（[Tag 06ZB](https://kerodon.net/tag/06ZB)）。対応表の状態：一部。

Cをpresentable、Wを宇宙小族にも強めるとbousfield\_isReflectiveSubcategoryは同じW-local部分圏のreflectivityを直接返す。指定λでの生成辺集合の等式全体は含まない。

:::

:::corollary "kerodon_9_6_3_12"
Kerodon Corollary 9.6.3.12（[Tag 06XT](https://kerodon.net/tag/06XT)）。対応表の状態：なし。

局所化による全関手の延長存在と充満忠実性は、原文のcocontinuousな両部分圏への同じ制限の比較を含まない。

宣言：`CategoryTheory.MorphismProperty.HasSmallObjectArgument`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_generatedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.exists_extension`

:::

# 9.6.4 Lifting Problems in ∞-Categories

%%%
number := false
tag := "kerodon-9-6-4"
%%%

Kerodon [Tag 04MH](https://kerodon.net/tag/04MH)

:::definition "kerodon_9_6_4_1"
Kerodon Definition 9.6.4.1（[Tag 04MK](https://kerodon.net/tag/04MK)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の可換正方形と解の構造はある。CatInfinity では四面体から合成の正方形を読む別の宣言があるが、任意の準圏で Δ¹×Δ¹ の指定の頂点配置を Δ³ へ延長する形の定義は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.CommSq`、`CategoryTheory.CommSq.LiftStruct`

:::

:::definition "kerodon_9_6_4_3"
Kerodon Notation 9.6.4.3（[Tag 04MN](https://kerodon.net/tag/04MN)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の正方形の解は対角射と二つの合成の等式を持つ。準圏で二面に加えてそれらを貼る 3 単体を指定する原文の解データは未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.CommSq.LiftStruct`

:::

:::definition "kerodon_9_6_4_8"
Kerodon Definition 9.6.4.8（[Tag 04MY](https://kerodon.net/tag/04MY)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では任意の可換正方形の対角射と整合の存在を表す持ち上げ性がある。準圏で全ての正方形の指定四面体延長を要求する弱直交は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.HasLiftingProperty`

:::

:::definition "kerodon_9_6_4_11"
Kerodon Variant 9.6.4.11（[Tag 04N1](https://kerodon.net/tag/04N1)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib の llp と rlp は通常圏の射のクラスに対して全称量化する。準圏内の弱直交と、それを二つのクラスへ拡張する定義は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.MorphismProperty.llp`、`CategoryTheory.MorphismProperty.rlp`

:::

:::proposition "kerodon_9_6_4_14"
Kerodon Proposition 9.6.4.14（[Tag 04N4](https://kerodon.net/tag/04N4)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の左持ち上げクラスは射圏の retract で閉じる。準圏の Fun(Δ¹,C) 内の retract と四面体の弱直交に対する結果は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.MorphismProperty.llp_isStableUnderRetracts`

:::

:::proposition "kerodon_9_6_4_15"
Kerodon Proposition 9.6.4.15（[Tag 04N5](https://kerodon.net/tag/04N5)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の左持ち上げクラスは pushout で閉じる。準圏における pushout と四面体での解の存在を結ぶ一般形は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.MorphismProperty.llp_isStableUnderCobaseChange`

:::

:::proposition "kerodon_9_6_4_16"
Kerodon Proposition 9.6.4.16（[Tag 04N7](https://kerodon.net/tag/04N7)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では任意の整列形状の超限合成で左持ち上げ性が保たれる。準圏の四面体解について極限順序数での連続性から弱直交を保つ結果は未確認。

宣言：`CategoryTheory.HasLiftingProperty`、`CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`

:::

:::definition "kerodon_9_6_4_17"
Kerodon Construction 9.6.4.17（[Tag 04NK](https://kerodon.net/tag/04NK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：頂点ファイバーと相対関手空間はある。原文で指定された四面体の部分複体 Q への制限と、その指定正方形 σ 上のファイバーを Sol とする構成は未確認。

宣言：`CategoryTheory.HasLiftingProperty`

:::

:::definition "kerodon_9_6_4_20"
Kerodon Construction 9.6.4.20（[Tag 04NU](https://kerodon.net/tag/04NU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：join の単体、相対カリー化、片側 coslice の三角形比較を調べた。両端を固定した二重 slice の写像空間から、Q 上の指定正方形を持つ四面体のファイバーへの比較 θ は未確認。

宣言：`CategoryTheory.HasLiftingProperty`

:::

:::proposition "kerodon_9_6_4_21"
Kerodon Proposition 9.6.4.21（[Tag 04NV](https://kerodon.net/tag/04NV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片側の三角形制限と twisted Hom の別の比較はある。二重 slice の写像空間から指定正方形の Sol への同じ θ が Kan ホモトピー同値となる型は未確認。

宣言：`CategoryTheory.HasLiftingProperty`

:::

:::corollary "kerodon_9_6_4_23"
Kerodon Corollary 9.6.4.23（[Tag 06W0](https://kerodon.net/tag/06W0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン・カルテシアン辺の持ち上げ性と逆圏比較を確認した。指定正方形の四面体解の全空間が U を通じて基底の解空間とホモトピー同値になる型は未確認。

宣言：`CategoryTheory.HasLiftingProperty`

:::

# 9.6.5 Weak Factorization Systems

%%%
number := false
tag := "kerodon-9-6-5"
%%%

Kerodon [Tag 04N9](https://kerodon.net/tag/04N9)

:::definition "kerodon_9_6_5_1"
Kerodon Definition 9.6.5.1（[Tag 04NA](https://kerodon.net/tag/04NA)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の弱分解系を、分解・retract 閉性・持ち上げの存在から構成できる。準圏で 2 単体により分解し四面体で持ち上げる構造は未確認。

宣言：`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`、`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`、`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk'`

:::

:::proposition "kerodon_9_6_5_5"
Kerodon Proposition 9.6.5.5（[Tag 04NE](https://kerodon.net/tag/04NE)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の弱分解系で両クラスが相手への持ち上げ性で特徴付けられる。準圏で弱直交により双方を特徴付ける型は未確認。

宣言：`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`、`CategoryTheory.MorphismProperty.rlp_eq_of_wfs`、`CategoryTheory.MorphismProperty.llp_eq_of_wfs`

:::

:::definition "kerodon_9_6_5_6"
Kerodon Definition 9.6.5.6（[Tag 04M2](https://kerodon.net/tag/04M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では三つの閉性の述語は別々にあり、準圏の強飽和性は余極限と二対三を使う。一般の W で準圏の pushout・retract・小超限合成の三条件を課す定義は未確認。

宣言：`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`

:::

:::theorem "kerodon_9_6_5_12"
Kerodon Theorem 9.6.5.12（[Tag 04NG](https://kerodon.net/tag/04NG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の分解と左クラスの記述、準圏の局所対象への強飽和置換はある。任意の presentable 準圏で弱飽和閉包と弱直交を両クラスとする分解系は未確認。

宣言：`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`

:::

# 9.6.6 Orthogonality

%%%
number := false
tag := "kerodon-9-6-6"
%%%

Kerodon [Tag 04NJ](https://kerodon.net/tag/04NJ)

:::definition "kerodon_9_6_6_1"
Kerodon Definition 9.6.6.1（[Tag 04NN](https://kerodon.net/tag/04NN)）。対応表の状態：なし。

IsLocalForHomは対象zへの前合成同値であり、原文の二つの任意射f,gの四つのHomのpullback条件そのものではない。gを終対象への射にした比較も型で未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::definition "kerodon_9_6_6_4"
Kerodon Variant 9.6.6.4（[Tag 04NT](https://kerodon.net/tag/04NT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の llp・rlp は解の存在を課し、準圏の局所性は特定の対象への前合成同値を課す。一般の二射の直交を二つの集合へ量化する原文の定義は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::definition "kerodon_9_6_6_7"
Kerodon Variant 9.6.6.7（[Tag 06W8](https://kerodon.net/tag/06W8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実性と CatInfinity の準圏性はある。原文の整数 n での圏論的連結性・n-faithfulness による CatInfinity 内の直交は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::proposition "kerodon_9_6_6_10"
Kerodon Proposition 9.6.6.10（[Tag 06WB](https://kerodon.net/tag/06WB)）。対応表の状態：なし。

対象局所性の合成・取消しは、任意の射gに対する直交性の同じpullback条件と比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_comp`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_cancel_left`

:::

:::proposition "kerodon_9_6_6_12"
Kerodon Proposition 9.6.6.12（[Tag 06WC](https://kerodon.net/tag/06WC)）。対応表の状態：なし。

localEquivalencesは全W-local対象への前合成同値を判定する。原文の指定一射gへの直交クラスとは異なる集合。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_arrowColimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_stronglySaturated`

:::

:::corollary "kerodon_9_6_6_13"
Kerodon Corollary 9.6.6.13（[Tag 04P3](https://kerodon.net/tag/04P3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱い持ち上げの retract 閉性と、準圏の余錐の retract による普遍性を確認した。任意の二射で可縮な解空間を持つ直交が Fun(Δ¹,C) の retract で保たれる型は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::corollary "kerodon_9_6_6_14"
Kerodon Corollary 9.6.6.14（[Tag 04P4](https://kerodon.net/tag/04P4)）。対応表の状態：なし。

対象zのlocalityのpushout保存は、原文の指定射gに対するHom四角のpullbackを同じものとする比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_pushout_right_of_left`

:::

:::corollary "kerodon_9_6_6_15"
Kerodon Corollary 9.6.6.15（[Tag 06WD](https://kerodon.net/tag/06WD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定した対象への局所性と通常圏の弱い持ち上げ性はある。任意の g の f への強直交から、f の相対余対角への強直交を得る宣言は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::definition "kerodon_9_6_6_16"
Kerodon Notation 9.6.6.16（[Tag 06WE](https://kerodon.net/tag/06WE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の Kan 標的への三角形評価と端点対のファイブレーション性はある。指定 f,g を固定した 3 点・4 点の Hom の三つの引戻しとそれぞれの自明 Kan ファイブレーション性は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::proposition "kerodon_9_6_6_18"
Kerodon Proposition 9.6.6.18（[Tag 06WG](https://kerodon.net/tag/06WG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：lax pullback の写像空間について厳密な引戻しと図式を構成する宣言はある。原文の f,g 付き三点・四点 Hom の正方形が、強直交を定義する Hom 正方形と同型になる比較は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::theorem "kerodon_9_6_6_19"
Kerodon Theorem 9.6.6.19（[Tag 06WJ](https://kerodon.net/tag/06WJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：lax pullback の写像空間の極限と、別の三角形空間の可縮性はある。指定の θ のホモトピー同値・自明 Kan 性と、各 Sol の可縮性を結ぶ五条件の iff は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::corollary "kerodon_9_6_6_23"
Kerodon Corollary 9.6.6.23（[Tag 06WL](https://kerodon.net/tag/06WL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：持ち上げ辺の比較と逆圏での交換はある。片側が指定持ち上げ辺のとき、基底の二射の強直交を全空間へ反映する型は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::corollary "kerodon_9_6_6_24"
Kerodon Corollary 9.6.6.24（[Tag 06WM](https://kerodon.net/tag/06WM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：三角形の評価と固定二辺の充填の可縮性を確認した。全ての指定正方形に対する二重 slice の写像空間の可縮性による強直交の判定は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::corollary "kerodon_9_6_6_25"
Kerodon Corollary 9.6.6.25（[Tag 04NY](https://kerodon.net/tag/04NY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の Hom 条件と slice 射影の一般論はある。任意の持ち上げ辺 f̃ で g を表す slice 対象が局所になる条件と、f と g の強直交を結ぶ iff は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::corollary "kerodon_9_6_6_26"
Kerodon Corollary 9.6.6.26（[Tag 04P8](https://kerodon.net/tag/04P8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱い持ち上げ性と、準圏の固定対象への局所性はある。S に相対余対角が残るとき、弱直交から任意の右側の射の強直交を復元する型は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

:::definition "kerodon_9_6_6_27"
Kerodon Notation 9.6.6.27（[Tag 06WP](https://kerodon.net/tag/06WP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：始点が点のとき coslice と Tw の始点固定部分を同値にする比較はある。両側の一般の図式 F,G を固定したときの、指定された二本のホモトピー同値と形状に関する関手性は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`

:::

# 9.6.7 Uniqueness of Factorizations

%%%
number := false
tag := "kerodon-9-6-7"
%%%

Kerodon [Tag 04PQ](https://kerodon.net/tag/04PQ)

:::definition "kerodon_9_6_7_1"
Kerodon Notation 9.6.7.1（[Tag 04PS](https://kerodon.net/tag/04PS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解のデータと、準圏の指定辺を保存する相対関手の部分圏はある。原文の Δ² の左・右短辺が任意の S\_L,S\_R に属する部分圏を個別に作り、その共通部分を取る宣言は未確認。

:::

:::theorem "kerodon_9_6_7_2"
Kerodon Theorem 9.6.7.2（[Tag 04QC](https://kerodon.net/tag/04QC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全三角形の内ホーン延長空間の可縮性と全部分圏の包含の充満忠実性はある。分解三角形の長辺への制限を、二つのクラスの直交で判定する iff は未確認。

:::

:::lemma_ "kerodon_9_6_7_3"
Kerodon Lemma 9.6.7.3（[Tag 06WS](https://kerodon.net/tag/06WS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：両端評価の写像空間と通常圏の持ち上げの構造を確認した。id\_X→g の指定された正方形との合成のホモトピー同値で強直交を判定する iff は未確認。

:::

:::proposition "kerodon_9_6_7_4"
Kerodon Proposition 9.6.7.4（[Tag 06WT](https://kerodon.net/tag/06WT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定短辺の三角形充填と Kan 標的への三角形長辺評価はある。異なる二つの分解三角形間の Hom の長辺制限が、左辺と相手の右辺の直交で同値になる型は未確認。

:::

# 9.6.8 Factorization Systems

%%%
number := false
tag := "kerodon-9-6-8"
%%%

Kerodon [Tag 04PC](https://kerodon.net/tag/04PC)

:::definition "kerodon_9_6_8_1"
Kerodon Definition 9.6.8.1（[Tag 04PD](https://kerodon.net/tag/04PD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系と、準圏の持ち上げ辺の構造を確認した。準圏での直交、2 単体の分解、矢印の同型閉性をまとめる強い分解系の述語は未確認。

:::

:::definition "kerodon_9_6_8_6"
Kerodon Variant 9.6.8.6（[Tag 06WY](https://kerodon.net/tag/06WY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の圏の模型、単体的集合の射の内アノダイン分解、充満忠実性はある。整数 n ごとの圏論的連結な関手と n-faithful な関手の強分解系は未確認。

:::

:::proposition "kerodon_9_6_8_8"
Kerodon Proposition 9.6.8.8（[Tag 04QD](https://kerodon.net/tag/04QD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定短辺の充填空間の可縮性と、通常圏の関手的分解データを確認した。原文の分解系の全三角形から長辺を取る写像の自明 Kan 性は未確認。

:::

:::corollary "kerodon_9_6_8_9"
Kerodon Corollary 9.6.8.9（[Tag 04QE](https://kerodon.net/tag/04QE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系の両クラスの持ち上げ性による記述はある。準圏の強分解系の両クラスが、全ての可逆辺を含む型は未確認。

:::

:::corollary "kerodon_9_6_8_10"
Kerodon Corollary 9.6.8.10（[Tag 04QF](https://kerodon.net/tag/04QF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の左・右持ち上げクラスは retract で閉じる。準圏の強分解系から Fun(Δ¹,C) 内の retract 閉性を得る型は未確認。

:::

:::corollary "kerodon_9_6_8_11"
Kerodon Corollary 9.6.8.11（[Tag 04QG](https://kerodon.net/tag/04QG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の retract と弱い持ち上げから弱分解系を組み立てる型はある。準圏の強分解系から retract 閉性と四面体解の存在を備えた弱分解系へ移す型は未確認。

:::

:::proposition "kerodon_9_6_8_13"
Kerodon Proposition 9.6.8.13（[Tag 04PJ](https://kerodon.net/tag/04PJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系では左クラスと弱い持ち上げが一致する。準圏の強分解系で、この一致に可縮な解空間の直交を加えた三条件の同値は未確認。

:::

:::corollary "kerodon_9_6_8_14"
Kerodon Corollary 9.6.8.14（[Tag 04PK](https://kerodon.net/tag/04PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱持ち上げクラスの pushout 閉性と、準圏の局所同値の閉性はある。弱分解系の強直交を左消去または相対余対角の閉性で判定する三条件は未確認。

:::

:::theorem "kerodon_9_6_8_15"
Kerodon Theorem 9.6.8.15（[Tag 04PT](https://kerodon.net/tag/04PT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解の選択と一般の圏同値判定はある。指定した全分解三角形の長辺制限が同値であることを含む三条件から準圏の分解系を回収する iff は未確認。

:::

:::corollary "kerodon_9_6_8_16"
Kerodon Corollary 9.6.8.16（[Tag 04PV](https://kerodon.net/tag/04PV)）。対応表の状態：なし。

通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏で関手的分解を各対象に適用して関手圏の分解を作れる。準圏の任意の単体集合形状について、点ごとの両クラスの強直交まで得る分解系は未確認。

宣言：`CategoryTheory.MorphismProperty.FunctorialFactorizationData.functorCategory`

:::

:::proposition "kerodon_9_6_8_17"
Kerodon Proposition 9.6.8.17（[Tag 04PL](https://kerodon.net/tag/04PL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の反変輸送の持ち上げと通常圏の分解データを確認した。カルテシアン右辺を指定して底の強分解系を全空間へ移す結果は未確認。

:::

# 9.6.9 Accessible Factorization Systems

%%%
number := false
tag := "kerodon-9-6-9"
%%%

Kerodon [Tag 06X2](https://kerodon.net/tag/06X2)

:::definition "kerodon_9_6_9_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes")
Kerodon Definition 9.6.9.2（[Tag 06X4](https://kerodon.net/tag/06X4)）。対応表の状態：一部。

IsStronglySaturatedEdgeSetOfShapesは同じSに2-of-3などを追加し、原文の同型包含・合成閉性・小arrow余極限閉性を直接与える。saturatedだけの全定義とは差がある。

:::

:::theorem "kerodon_9_6_9_8"
Kerodon Theorem 9.6.9.8（[Tag 04PN](https://kerodon.net/tag/04PN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族からの強飽和な局所同値とその射圏部分の presentability はある。任意の飽和生成クラスと元の W に強直交する右クラスを対にした準圏の分解系は未確認。

:::

:::proposition "kerodon_9_6_9_10"
Kerodon Proposition 9.6.9.10（[Tag 06XB](https://kerodon.net/tag/06XB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の生成辺の Ind 像の包含が accessible になる結果はある。任意の分解系の左・右の accessibly embedded 性と、長辺制限の切断の accessibility を結ぶ三条件は未確認。

:::

:::definition "kerodon_9_6_9_11"
Kerodon Definition 9.6.9.11（[Tag 06XC](https://kerodon.net/tag/06XC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解と準圏の関手の accessibility は別々にある。分解系のいずれかのクラスの包含または分解の切断に accessibility を課す定義は未確認。

:::

:::proposition "kerodon_9_6_9_12"
Kerodon Proposition 9.6.9.12（[Tag 06XD](https://kerodon.net/tag/06XD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族からの強飽和閉包の射圏と、通常圏の小対象論法を確認した。準圏の accessible 分解系を、右クラスを強直交で決める小さい辺族の存在と同値にする型は未確認。

:::

:::proposition "kerodon_9_6_9_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory_isPresentable")
Kerodon Proposition 9.6.9.13（[Tag 06XE](https://kerodon.net/tag/06XE)）。対応表の状態：一部。

Wbarを同じ小族からのgeneratedEdgesとしgeneratedArrowCategoryを取る場合、presentabilityは原文(3)の同じarrow部分圏のaccessibilityを直接返す。任意のsaturatedクラスの全iffは含まない。

:::

:::corollary "kerodon_9_6_9_14"
Kerodon Corollary 9.6.9.14（[Tag 06XF](https://kerodon.net/tag/06XF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の強飽和な局所同値の記述と、通常圏の弱分解系での左クラスの一意性を確認した。原文の accessible な強分解系と accessibly saturated クラスの全単射は未確認。

:::

:::definition "kerodon_9_6_9_15"
Kerodon Variant 9.6.9.15（[Tag 06XG](https://kerodon.net/tag/06XG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の左クラスの記述と両クラスの直交による特徴付けはある。準圏で小辺族から作る弱飽和クラスと弱分解系の全単射は未確認。

:::

:::definition "kerodon_9_6_9_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_stronglySaturated")
Kerodon Definition 9.6.9.18（[Tag 06XK](https://kerodon.net/tag/06XK)）。対応表の状態：本体にある。

仮定：Quasicategory X と辺の集合、Lean では余極限形状を引数に取る。小形状を全て選ぶ場合が原文（Lean が弱い）。結論：同値辺を含み二つから三つ、矢の図式の指定形状の余極限に閉じる強飽和性（全小形状の場合は原文と一致）。

:::

:::proposition "kerodon_9_6_9_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_stronglySaturated")
Kerodon Proposition 9.6.9.23（[Tag 06XQ](https://kerodon.net/tag/06XQ)）。対応表の状態：一部。

小Wから生成した同じgeneratedEdgesについてlocalEquivalencesとの等式とstrong saturationは、原文のlocal equivalence表示とstrong saturationの成分を直接与える。小集合によるcolimit生成を含む全三条件の同値は含まない。

:::

:::corollary "kerodon_9_6_9_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory")
Kerodon Corollary 9.6.9.25（[Tag 06XS](https://kerodon.net/tag/06XS)）。対応表の状態：一部。

小Wに対するlocal部分圏と生成辺集合の等式は、原文の対応の同じ小生成入力に対する値を直接与える。全Bousfield部分圏からの回収と全単射の型は含まない。

:::

