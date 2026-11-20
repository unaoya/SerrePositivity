-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianSections
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.FilteredColimitFiniteLimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.7 Universality of Colimits" =>
%%%
number := false
tag := "kerodon-7-7"
%%%

Kerodon の 7.7 節（[Tag 05SB](https://kerodon.net/tag/05SB)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_7_7_0_1"
Kerodon Definition 7.7.0.1（[Tag 05SE](https://kerodon.net/tag/05SE)）。対応表の状態：なし。

MathlibのIsUniversalColimitは通常圏のNatTransとIsPullbackで定義される。原文の∞圏の指定βとlevelwise pullbackとの比較がない。

宣言：`CategoryTheory.IsUniversalColimit`

:::

:::theorem "kerodon_7_7_0_4" (uses := "kerodon_1_4_0_1, kerodon_3_1_6_1")
Kerodon Theorem 7.7.0.4（[Tag 05SH](https://kerodon.net/tag/05SH)）。対応表の状態：なし。

span円筒と単射列の自然性squareのhomotopy pullback保存は部品。原文の全小図式についてcartesian変換の切断準圏の制限が同値となるstrongly universalの結論に直接は達しない。

宣言：`SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback`、`SerrePositivity.KST.Comparison.sequential_homotopyPullback`

:::

:::corollary "kerodon_7_7_0_6" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_6_2_40, kerodon_7_7_0_4")
Kerodon Corollary 7.7.0.6（[Tag 05SK](https://kerodon.net/tag/05SK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類での基底変換は κ-filtered 余極限を保ち、空間値図式の全空間モデルは余極限を与える。任意の β の余極限性と全点ファイバーの可縮余極限を含む四条件の iff は見つからない。

:::

# 7.7.1 Cartesian Natural Transformations

%%%
number := false
tag := "kerodon-7-7-1"
%%%

Kerodon [Tag 05SL](https://kerodon.net/tag/05SL)

:::definition "kerodon_7_7_1_1"
Kerodon Definition 7.7.1.1（[Tag 05SM](https://kerodon.net/tag/05SM)）。対応表の状態：なし。

NatTrans.Equifiberedは通常圏のstrict自然性squareを判定する述語。原文の∞圏の指定自然変換の各2単体のpullback条件との比較がない。

宣言：`CategoryTheory.NatTrans.Equifibered`

:::

:::proposition "kerodon_7_7_1_13"
Kerodon Proposition 7.7.1.13（[Tag 05T0](https://kerodon.net/tag/05T0)）。対応表の状態：なし。

通常圏のEquifiberedの定義は、原文のK▷上の同じ自然変換のcartesian性と頂点への制限のlevelwise pullback性のiffを結論しない。

宣言：`CategoryTheory.NatTrans.Equifibered`

:::

:::definition "kerodon_7_7_1_14"
Kerodon Variant 7.7.1.14（[Tag 05T1](https://kerodon.net/tag/05T1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の辺ごとの引き戻し述語と join 余錐の頂点への収縮はある。指定 γ の cartesian 性と定値図式への点ごとの引き戻し表示を比較する型は見つからない。

:::

:::definition "kerodon_7_7_1_15"
Kerodon Definition 7.7.1.15（[Tag 05T3](https://kerodon.net/tag/05T3)）。対応表の状態：なし。

通常圏のIsUniversalColimitは、原文の任意のcartesianな増強自然変換による∞余極限性の定義と比較する型を持たない。

宣言：`CategoryTheory.IsUniversalColimit`

:::

:::proposition "kerodon_7_7_1_19"
Kerodon Proposition 7.7.1.19（[Tag 05T7](https://kerodon.net/tag/05T7)）。対応表の状態：なし。

通常圏のIsUniversalColimitの定義だけでは、原文の指定∞自然変換βについての二表現のiffに接続しない。

宣言：`CategoryTheory.IsUniversalColimit`

:::

:::corollary "kerodon_7_7_1_20"
Kerodon Corollary 7.7.1.20（[Tag 05T9](https://kerodon.net/tag/05T9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の一つの余錐に対する基底変換閉性は定義される。任意の∞圏の形状 K で全余極限がその性質を持つことと、圏の K-余極限の普遍性を比較する型は見つからない。

:::

:::definition "kerodon_7_7_1_21"
Kerodon Definition 7.7.1.21（[Tag 05TA](https://kerodon.net/tag/05TA)）。対応表の状態：なし。

通常圏のIsUniversalColimitの存在と原文の∞圏の指定図式のuniversal colimit diagramの存在との比較がない。

宣言：`CategoryTheory.IsUniversalColimit`

:::

# 7.7.2 Descent Diagrams

%%%
number := false
tag := "kerodon-7-7-2"
%%%

Kerodon [Tag 05TC](https://kerodon.net/tag/05TC)

:::definition "kerodon_7_7_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
Kerodon Notation 7.7.2.1（[Tag 05TD](https://kerodon.net/tag/05TD)）。対応表の状態：一部。

*主張*　単体集合のデカルトファイブレーション $`U:E\to C` と $`F:K\to C` に対し、$`C` 上の持ち上げの無限圏で、$`K` の全辺を $`U`-デカルト辺へ送る持ち上げが張る充満部分圏を $`\operatorname{Fun}_{/C}^{\mathrm{ACart}}(K,E)` と書く。

relativeFunctorSpace U Fは原文の底上の同じ全関手単体集合を直接構成する。cartesian fibrationならinnerなのでその準圏性も既存instanceで得る。cartesianな全辺という頂点条件の全部分圏は、引用のcocartesianSectionsで代用しない。

:::

:::definition "kerodon_7_7_2_5"
Kerodon Definition 7.7.2.5（[Tag 05TJ](https://kerodon.net/tag/05TJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：双対の cocartesian 切断を前合成で制限する射と充満忠実の述語はある。K▷→K の cartesian 切断制限に対する descent と effective descent の二定義は見つからない。

:::

:::theorem "kerodon_7_7_2_8"
Kerodon Theorem 7.7.2.8（[Tag 05TL](https://kerodon.net/tag/05TL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余極限の普遍性と、双対の切断制限は別々にある。ev₁ に対する descent の順方向と、K-余極限または終対象を仮定した逆方向は見つからない。

:::

:::definition "kerodon_7_7_2_10"
Kerodon Notation 7.7.2.10（[Tag 05TN](https://kerodon.net/tag/05TN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の equifibered 述語と頂点が張る部分複体の一般構成はある。Fun(K,C) の指定スライスで cartesian な γ のみを集めた充満部分圏は見つからない。

:::

:::corollary "kerodon_7_7_2_12"
Kerodon Corollary 7.7.2.12（[Tag 05TQ](https://kerodon.net/tag/05TQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の普遍余極限述語と準圏の充満忠実はある。任意の指定余極限に対する cartesian なスライスの制限が充満忠実であることとの同値は見つからない。

:::

:::definition "kerodon_7_7_2_13"
Kerodon Definition 7.7.2.13（[Tag 05TR](https://kerodon.net/tag/05TR)）。対応表の状態：なし。

IsVanKampenColimitは通常圏のIsColimit/IsPullbackのiffであり、原文のcartesianな関手の切断準圏の制限の圏同値性と同じ条件への比較を持たない。

宣言：`CategoryTheory.IsVanKampenColimit`

:::

:::definition "kerodon_7_7_2_15"
Kerodon Definition 7.7.2.15（[Tag 05TT](https://kerodon.net/tag/05TT)）。対応表の状態：なし。

通常圏のvan Kampen余錐は、原文の∞圏の指定colimitのstrongly universal性と選択不変性への比較がない。

宣言：`CategoryTheory.IsVanKampenColimit`

:::

:::corollary "kerodon_7_7_2_19"
Kerodon Corollary 7.7.2.19（[Tag 05TX](https://kerodon.net/tag/05TX)）。対応表の状態：なし。

通常圏のvan Kampen条件は原文の∞圏のcartesian変換の条件と比較されていない。形式が類似するiffだけでは数えない。

宣言：`CategoryTheory.IsVanKampenColimit`

:::

:::corollary "kerodon_7_7_2_23"
Kerodon Corollary 7.7.2.23（[Tag 05U1](https://kerodon.net/tag/05U1)）。対応表の状態：なし。

通常のIsVanKampenColimitを全余錐で量化しても、原文の同じ∞圏の強普遍性とcartesian変換のiffへの比較がない。

宣言：`CategoryTheory.IsVanKampenColimit`

:::

:::definition "kerodon_7_7_2_24"
Kerodon Definition 7.7.2.24（[Tag 05U2](https://kerodon.net/tag/05U2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意に与えたスライス余錐を元の圏への射影で判定する。K⋆Δ¹ の縮退から指定した lift を作り、それにより弱余極限を定義する型は見つからない。

:::

:::proposition "kerodon_7_7_2_26"
Kerodon Proposition 7.7.2.26（[Tag 05U4](https://kerodon.net/tag/05U4)）。対応表の状態：なし。

sliceOver\_isColimitCone\_iff\_projectionは既に与えたslice余錐の極限性を比較する。原文のweak colimitを定める縮退による指定liftとの同定と、任意のFからそのliftを得る型を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection`

:::

:::corollary "kerodon_7_7_2_28"
Kerodon Corollary 7.7.2.28（[Tag 05U6](https://kerodon.net/tag/05U6)）。対応表の状態：なし。

引用は固定sliceの一余錐と射影の余極限性のiff。原文のweak colimitという指定標準liftの条件および全lift/あるliftの量化への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection`

:::

:::corollary "kerodon_7_7_2_30"
Kerodon Corollary 7.7.2.30（[Tag 05U8](https://kerodon.net/tag/05U8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 性を仮定した四つの Hom の引き戻し比較はある。弱余極限図式を入力に、cartesian な相手に対するスライス Hom の制限を同値にする iff は見つからない。

:::

:::corollary "kerodon_7_7_2_31"
Kerodon Corollary 7.7.2.31（[Tag 05U9](https://kerodon.net/tag/05U9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定スライス余錐の余極限性を台で判定する。ev₁ の descent と、全 cartesian な変換の上側が弱余極限となる条件の iff は見つからない。

:::

:::corollary "kerodon_7_7_2_32"
Kerodon Corollary 7.7.2.32（[Tag 05UA](https://kerodon.net/tag/05UA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で引き戻しが後合成の右随伴になる。∞圏の向き付きスライスに lift した指定図式の余極限性を全 u\* に要求する descent 判定は見つからない。

:::

:::corollary "kerodon_7_7_2_33"
Kerodon Corollary 7.7.2.33（[Tag 05UC](https://kerodon.net/tag/05UC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類の特定の基底変換が κ-filtered 余極限を保つ。任意のスライス引き戻しの保存と全弱余極限の descent との iff は見つからない。

:::

:::corollary "kerodon_7_7_2_34"
Kerodon Corollary 7.7.2.34（[Tag 05UD](https://kerodon.net/tag/05UD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余錐の引き戻し不変性と、左ファイブレーション分類の κ-filtered 保存を確認した。任意の∞圏の K-余極限が普遍であることと全 u\* の K-余極限保存の iff は見つからない。

:::

# 7.7.3 Cartesian Closed ∞-Categories

%%%
number := false
tag := "kerodon-7-7-3"
%%%

Kerodon [Tag 05UE](https://kerodon.net/tag/05UE)

:::definition "kerodon_7_7_3_1" (lean := "CategoryTheory.Closed, CategoryTheory.MonoidalClosed")
Kerodon Definition 7.7.3.1（[Tag 05UF](https://kerodon.net/tag/05UF)）。対応表の状態：Mathlib にある。

*主張*　有限積を持つ通常の圏で、評価 $`e:M\times X\to Y` が指数対象を与えるとは、任意の $`c` で $`c\to M` を $`c\times X\to M\times X\to Y` に送る操作が全単射であることをいう。有限積を持ち、任意の $`X,Y` に指数対象が存在する圏をデカルト閉圏と呼ぶ。

仮定：通常圏に有限積を選び、それを CartesianMonoidalCategory のテンソルとする。Closed と MonoidalClosed の型は一般のモノイダル積も許す（Lean が弱い）。結論：Closed X は X とのテンソルの右随伴を与え、Hom の随伴全単射は評価射との合成。全 X にこれを要求する MonoidalClosed（原文の Cartesian closed 性と一致）。

:::

:::definition "kerodon_7_7_3_4"
Kerodon Definition 7.7.3.4（[Tag 05UJ](https://kerodon.net/tag/05UJ)）。対応表の状態：なし。

Closed/MonoidalClosedは通常圏のHom集合の随伴で、原文の∞圏の同じ評価射による全写像空間のホモトピー同値への比較がない。

宣言：`CategoryTheory.Closed`、`CategoryTheory.MonoidalClosed`

:::

:::proposition "kerodon_7_7_3_13"
Kerodon Proposition 7.7.3.13（[Tag 05UT](https://kerodon.net/tag/05UT)）。対応表の状態：なし。

通常圏のtoOverSectionsAdjは原文の∞圏の指数対象と指定slice準圏の関手の右随伴への比較を持たない。

宣言：`CategoryTheory.forgetAdjToOver`、`CategoryTheory.Over.toOverSectionsAdj`

:::

:::definition "kerodon_7_7_3_14"
Kerodon Definition 7.7.3.14（[Tag 05UV](https://kerodon.net/tag/05UV)）。対応表の状態：なし。

ExponentiableMorphismは通常圏の選んだpullback関手の右随伴の条件。原文の全slice準圏のcartesian closed性への比較がない。

宣言：`CategoryTheory.ExponentiableMorphism`

:::

:::proposition "kerodon_7_7_3_17"
Kerodon Proposition 7.7.3.17（[Tag 05UY](https://kerodon.net/tag/05UY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の指数可能な射の右随伴データと空間圏の小極限はある。SpaceInfinity の各スライスが Cartesian closed である型は見つからない。

:::

:::proposition "kerodon_7_7_3_19"
Kerodon Proposition 7.7.3.19（[Tag 05V1](https://kerodon.net/tag/05V1)）。対応表の状態：なし。

通常圏のpullbackPushforwardAdjは原文の∞圏のsliceの同じf\*の右随伴との型の比較を含まない。

宣言：`CategoryTheory.ExponentiableMorphism`、`CategoryTheory.ExponentiableMorphism.isExponentiable`

:::

:::corollary "kerodon_7_7_3_20"
Kerodon Corollary 7.7.3.20（[Tag 05V2](https://kerodon.net/tag/05V2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で指数可能な射の引き戻しを左随伴にし、左随伴は余極限を保つ。∞圏の ev₁ に対する弱余極限の descent を得る型は見つからない。

:::

:::corollary "kerodon_7_7_3_21"
Kerodon Corollary 7.7.3.21（[Tag 05V3](https://kerodon.net/tag/05V3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の引き戻しが左随伴であれば余極限を保つ。終対象または K-余極限存在を仮定した∞圏で、K-余極限の普遍性までを述べる型は見つからない。

:::

:::corollary "kerodon_7_7_3_23"
Kerodon Corollary 7.7.3.23（[Tag 05V5](https://kerodon.net/tag/05V5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類の特定の基底変換で κ-filtered 余極限の保存はある。SpaceInfinity で任意の小形状の余極限が普遍である型は見つからない。

:::

# 7.7.4 Disjoint Coproducts

%%%
number := false
tag := "kerodon-7-7-4"
%%%

Kerodon [Tag 05V6](https://kerodon.net/tag/05V6)

:::definition "kerodon_7_7_4_1"
Kerodon Definition 7.7.4.1（[Tag 05V7](https://kerodon.net/tag/05V7)）。対応表の状態：なし。

CoproductDisjointの通常圏のMonoとIsInitialなstrict pullbackは、原文の∞圏の同じ余積・monomorphism・pullback条件との比較がない。

宣言：`CategoryTheory.Limits.CoproductDisjoint`

:::

:::definition "kerodon_7_7_4_5"
Kerodon Definition 7.7.4.5（[Tag 05VC](https://kerodon.net/tag/05VC)）。対応表の状態：なし。

通常圏のBinaryCoproductsDisjointは、原文の始対象と∞圏の二項余積の非交差性への型の比較を持たない。

宣言：`CategoryTheory.Limits.BinaryCoproductsDisjoint`

:::

:::definition "kerodon_7_7_4_8"
Kerodon Variant 7.7.4.8（[Tag 05VF](https://kerodon.net/tag/05VF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で各余射影が単射かつ相異なる射影の引き戻しが始対象なら非交差余積を得る。CatInfinity の余積とその二射影がこの条件を満たす型は見つからない。

:::

:::proposition "kerodon_7_7_4_9"
Kerodon Proposition 7.7.4.9（[Tag 05VG](https://kerodon.net/tag/05VG)）。対応表の状態：なし。

通常圏のCoproductDisjoint.of\_hasCoproductは原文の∞圏の二項非交差性から任意の同じIへの推論を結論しない。

宣言：`CategoryTheory.Limits.CoproductDisjoint.of_hasCoproduct`

:::

:::proposition "kerodon_7_7_4_10"
Kerodon Proposition 7.7.4.10（[Tag 05VJ](https://kerodon.net/tag/05VJ)）。対応表の状態：なし。

通常圏のvan Kampenと始対象のpullbackの結果は、原文の∞圏のstrongly universal性と非交差性のiffへの比較を持たない。

宣言：`CategoryTheory.BinaryCofan.isVanKampen_iff`、`CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`

:::

:::corollary "kerodon_7_7_4_11"
Kerodon Corollary 7.7.4.11（[Tag 05VK](https://kerodon.net/tag/05VK)）。対応表の状態：なし。

通常圏のvan Kampen⇒universalと余射影のpullbackの始性は、原文の∞圏の三条件の同じ強普遍性への比較を欠く。

宣言：`CategoryTheory.IsVanKampenColimit.isUniversal`、`CategoryTheory.isPullback_initial_to_of_cofan_isVanKampen`

:::

:::corollary "kerodon_7_7_4_12"
Kerodon Corollary 7.7.4.12（[Tag 05VL](https://kerodon.net/tag/05VL)）。対応表の状態：なし。

通常のTypeの有限余積のvan Kampen性は、原文のSpaceまたはQC内の余積の強普遍性と同じ述語ではなく、その比較もない。

宣言：`CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`、`CategoryTheory.types.finitaryExtensive`

:::

# 7.7.5 The Mather Cube Theorem Revisted

%%%
number := false
tag := "kerodon-7-7-5"
%%%

Kerodon [Tag 05VM](https://kerodon.net/tag/05VM)

:::definition "kerodon_7_7_5_1"
Kerodon Definition 7.7.5.1（[Tag 05VN](https://kerodon.net/tag/05VN)）。対応表の状態：なし。

通常圏のIsPushout.IsVanKampenはstrict cubeの条件。原文の∞圏のcoherentなcubeの二条件との比較を持たない。

宣言：`CategoryTheory.IsPushout.IsVanKampen`

:::

:::proposition "kerodon_7_7_5_6"
Kerodon Proposition 7.7.5.6（[Tag 05VU](https://kerodon.net/tag/05VU)）。対応表の状態：なし。

通常圏の厳密始対象のvan Kampen性は、原文の∞圏の全有限余極限の普遍性と二条件のiffに直接接続しない。

宣言：`CategoryTheory.IsInitial.isVanKampenColimit`、`CategoryTheory.IsVanKampenColimit.isUniversal`

:::

:::definition "kerodon_7_7_5_7"
Kerodon Variant 7.7.5.7（[Tag 05VV](https://kerodon.net/tag/05VV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の立方体判定と指定余錐の普遍性はある。κ-small な全余極限を κ-small 余積と第二立方体条件に還元する型は見つからない。

:::

:::proposition "kerodon_7_7_5_8"
Kerodon Proposition 7.7.5.8（[Tag 05VW](https://kerodon.net/tag/05VW)）。対応表の状態：なし。

通常圏のvan Kampenな始対象とcube条件は、原文の∞圏の二Mather条件による全有限余極限の強普遍性と比較されていない。

宣言：`CategoryTheory.IsInitial.isVanKampenColimit`、`CategoryTheory.IsPushout.IsVanKampen`

:::

:::corollary "kerodon_7_7_5_9"
Kerodon Corollary 7.7.5.9（[Tag 05VX](https://kerodon.net/tag/05VX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で指定押し出しの立方体条件と個別余錐の普遍性を記述する。両立方体条件と κ-small 余積の普遍性で全 κ-small 余極限を判定する型は見つからない。

:::

:::corollary "kerodon_7_7_5_10"
Kerodon Corollary 7.7.5.10（[Tag 05VY](https://kerodon.net/tag/05VY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の小余完備性と通常圏の van Kampen 述語はある。空間圏の全小余極限が強普遍である型は見つからない。

:::

# 7.7.6 Descent in the ∞-Category of Spaces

%%%
number := false
tag := "kerodon-7-7-6"
%%%

Kerodon [Tag 05VZ](https://kerodon.net/tag/05VZ)

:::theorem "kerodon_7_7_6_1"
Kerodon Theorem 7.7.6.1（[Tag 05W0](https://kerodon.net/tag/05W0)）。対応表の状態：なし。

span・単射列・fat realizationのhomotopy pullback保存は部品。原文の指定Space余錐がstrongly universalであるという切断準圏の制限同値を直接結論しない。

宣言：`SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback`、`SerrePositivity.KST.Comparison.spanPushout_vertex_homotopyPullback`、`SerrePositivity.KST.Comparison.sequential_homotopyPullback`、`SerrePositivity.KST.Comparison.fatRealizationInclusion_homotopyPullback`

:::

:::proposition "kerodon_7_7_6_2"
Kerodon Proposition 7.7.6.2（[Tag 05W1](https://kerodon.net/tag/05W1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの可縮ファイバーと filtered な底から全空間の Kan 置換が可縮となる。二つの引き戻しで指定された包含の弱同値性と延長射影の Kan 性を比較する iff は見つからない。

:::

:::lemma_ "kerodon_7_7_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_equivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_innerFibration")
Kerodon Lemma 7.7.6.3（[Tag 05W3](https://kerodon.net/tag/05W3)）。対応表の状態：一部。

*主張*　同じ単体集合上の二つの左ファイブレーションの間の射は、同型ファイブレーションであるとき、かつそのときに限り左ファイブレーションである。

E′,Eを準圏に強めると、Γ自身がleft fibration⇒innerかつEquivalenceLiftingという二宣言が同じΓのisofibration性を直接与える。isofibration⇒left fibrationおよび任意の単体集合上ではない。

:::

:::proposition "kerodon_7_7_6_5"
Kerodon Proposition 7.7.6.5（[Tag 05W6](https://kerodon.net/tag/05W6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい左ファイブレーションの表現間で相対 Hom と変換空間を比較する型はある。Γ の Kan 性、Δ¹ の終点制限、各辺の引き戻し、γ の cartesian 性を比較する iff は見つからない。

:::

:::proposition "kerodon_7_7_6_6"
Kerodon Proposition 7.7.6.6（[Tag 05W9](https://kerodon.net/tag/05W9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙での空間の小余極限はある。cf(λ)-small な形状で S\_\{\<λ\} の各余極限が強普遍となる型は見つからない。

:::

:::proposition "kerodon_7_7_6_7"
Kerodon Proposition 7.7.6.7（[Tag 05WA](https://kerodon.net/tag/05WA)）。対応表の状態：なし。

通常圏のIsVanKampenColimitのiffは、原文のS\_\<λの指定増強自然変換のcartesian性と余極限性への比較を持たない。

宣言：`CategoryTheory.IsVanKampenColimit`

:::

# 7.7.7 Digression: Commutation of Limits and Colimits

%%%
number := false
tag := "kerodon-7-7-7"
%%%

Kerodon [Tag 05XG](https://kerodon.net/tag/05XG)

:::proposition "kerodon_7_7_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_6_17, kerodon_7_1_8_2")
Kerodon Proposition 7.7.7.1（[Tag 05XH](https://kerodon.net/tag/05XH)）。対応表の状態：一部。

*主張*　無限圏 $`C` が $`K` 添字の余極限と $`L` 添字の極限を持つとする。極限関手が $`K` 添字の余極限を保つこと、$`L` の左錐の極限図式の充満部分圏がその余極限で閉じること、余極限関手が $`L` 添字の極限を保つこと、$`K` の右錐の余極限図式の充満部分圏がその極限で閉じることは同値である。

CをSpace、Kを小さいfiltered準圏、Lを有限形状に限るとsmallSpaceFilteredColimit\_map\_isLimit\_finiteは同じcolimit functorのL極限保存（7.7.7.1の条件(3)）を直接返す。任意K,Lの四条件の全同値と閉性の判定は含まない。

:::

:::definition "kerodon_7_7_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite")
Kerodon Definition 7.7.7.2（[Tag 05XJ](https://kerodon.net/tag/05XJ)）。対応表の状態：一部。

*主張*　無限圏が $`K` 添字の余極限と $`L` 添字の極限を持つとき、7.7.7.1 の同値な条件を満たすことを、$`K` 添字の余極限と $`L` 添字の極限が可換であるという。

CをSpace、Kを小さいfiltered準圏、Lを有限形状に限るとsmallSpaceFilteredColimit\_map\_isLimit\_finiteは同じcolimit functorのL極限保存（7.7.7.1の条件(3)）を直接返す。任意K,Lの四条件の全同値と閉性の判定は含まない。

:::

:::proposition "kerodon_7_7_7_3"
Kerodon Proposition 7.7.7.3（[Tag 05XK](https://kerodon.net/tag/05XK)）。対応表の状態：なし。

filtered余極限の有限極限保存はあるが、原文の「余極限が可縮な図式を張る全部分圏」の閉性を型に含まない。片側の交換性だけの証明はこのiffの一方向ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite`、`CategoryTheory.Limits.filtered_colim_preservesFiniteLimits`

:::

:::definition "kerodon_7_7_7_4" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_7_0_6")
Kerodon Variant 7.7.7.4（[Tag 05XL](https://kerodon.net/tag/05XL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：切断で検出する局所対象の極限閉性と、固定宇宙の空間の小極限はある。濃度 μ の空間値関手のうち可縮余極限を持つ充満部分圏の極限閉性と、K-余極限・L-極限の交換との iff は見つからない。

:::

