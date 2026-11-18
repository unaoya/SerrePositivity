import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.DoubleMappingCylinder
import SerrePositivity.KST.Comparison.AlternativeFiberCriterion
import SerrePositivity.KST.Comparison.AlternativePullback
import SerrePositivity.KST.Comparison.DoubleMappingCylinderCollapse
import SerrePositivity.KST.Comparison.DoubleMappingCylinderEquivalence
import SerrePositivity.KST.Comparison.FibrantCospanInvariance
import SerrePositivity.KST.Comparison.FreeDegeneracies
import SerrePositivity.KST.Comparison.FreeDegeneraciesEquivalence
import SerrePositivity.KST.Comparison.HomotopyPullback
import SerrePositivity.KST.Comparison.HomotopyPullbackGeneralPasting
import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry
import SerrePositivity.KST.Comparison.LocalizedPushoutCube
import SerrePositivity.KST.Comparison.SpanPushoutGluing
import SerrePositivity.KST.Fibration.PullbackCancellation
import SerrePositivity.KST.SConstruction.SimplicialProductQuillenA

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "3.4 Homotopy Pullback and Homotopy Pushout Squares" =>
%%%
number := false
tag := "kerodon-3-4"
%%%

Kerodon の 3.4 節（[Tag 0106](https://kerodon.net/tag/0106)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_3_4_0_2" (lean := "SerrePositivity.KST.Comparison.fibrantCospanMap_localized_isIso")
Kerodon Proposition 3.4.0.2（[Tag 0109](https://kerodon.net/tag/0109)）。対応表の状態：本体にある。

仮定：二つの単体集合の cospan で指定側の脚が Kan fibration、三頂点の比較射が弱ホモトピー同値（Kerodon と一致。Lean は J.rlp と anodyne 局所化同型で記述）。結論：両射影と整合する通常の引き戻しの比較射が局所化同型で、同じ射が弱ホモトピー同値（一致）。

:::

:::definition "kerodon_3_4_0_3" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Construction 3.4.0.3（[Tag 010B](https://kerodon.net/tag/010B)）。対応表の状態：なし。

B6：anodyne–Kan 置換による pullback と equivalencePathReplacement は、原文の全区間写像を使う特定の二重 pullback との比較がない別模型。 候補：homotopyPullbackObject は右脚を anodyne–Kan 分解してから引き戻す。equivalencePathReplacement は可逆 path を使う別模型。Kerodon の全区間写像 X\^Δ¹ に沿う両端の具体的な引き戻しとの同定は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement`、`SerrePositivity.KST.Comparison.homotopyPullbackObject`

:::

:::proposition "kerodon_3_4_0_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_6, kerodon_3_4_0_2")
Kerodon Proposition 3.4.0.7（[Tag 0329](https://kerodon.net/tag/0329)）。対応表の状態：なし。

B6：原文の指定の通常pullback→全区間模型の射との比較がない。 候補：一脚が Kan fibration のとき通常の引き戻しがホモトピー引き戻しになる。原文の Kan 底の全区間写像を使う模型への指定の包含との同定は未確認。

宣言：`SerrePositivity.KST.Comparison.isHomotopyPullback_of_fibration`

:::

:::proposition "kerodon_3_4_0_9" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_3, kerodon_3_4_0_2")
Kerodon Proposition 3.4.0.9（[Tag 032B](https://kerodon.net/tag/032B)）。対応表の状態：なし。

B6：右脚を置換する模型の比較射であり、原文の区間模型の比較射との自然な同定がない。 候補：三頂点の局所化同型から選んだ右脚の Kan 置換を使う引き戻しの比較が局所化同型。原文の区間写像模型での比較との自然な同定は未確認。

宣言：`SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso`

:::

# 3.4.1 Homotopy Pullback Squares

%%%
number := false
tag := "kerodon-3-4-1"
%%%

Kerodon [Tag 010K](https://kerodon.net/tag/010K)

:::definition "kerodon_3_4_1_1" (lean := "SerrePositivity.KST.Comparison.IsHomotopyPullback, SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative")
Kerodon Definition 3.4.1.1（[Tag 010L](https://kerodon.net/tag/010L)）。対応表の状態：本体にある。

仮定：任意の可換正方形（Kerodon と一致）。結論：片脚の弱同値・Kan fibration 分解を経た通常の引き戻しへの比較の局所化同型性で IsHomotopyPullback を定める。別の分解でも同値な判定を与える（一致。局所化同型を同じ射の弱ホモトピー同値と比較）。

:::

:::proposition "kerodon_3_4_1_2" (lean := "SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative, SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber")
Kerodon Proposition 3.4.1.2（[Tag 010N](https://kerodon.net/tag/010N)）。対応表の状態：本体にある。

仮定：可換正方形、片脚の局所化同型と J.rlp による分解、その厳密な引き戻しと整合する比較射（Kerodon と一致）。結論：元の正方形の IsHomotopyPullback と分解後の引き戻しへの比較の局所化同型性が同値（一致）。

:::

:::corollary "kerodon_3_4_1_5" (uses := "kerodon_1_1_0_6, kerodon_3_4_1_2")
Kerodon Corollary 3.4.1.5（[Tag 010Q](https://kerodon.net/tag/010Q)）。対応表の状態：なし。

B6：IsHomotopyPullback の定義と右固有性は原文の任意の正方形の iff を直接述べず、区間模型との比較が必要。 候補：一般の引き戻しの比較の型と、Kan fibration に沿う弱同値の引き戻しはある。右脚が弱同値の正方形で左脚の弱同値性とホモトピー引き戻し性を直接同値にする宣言は未確認。

宣言：`SerrePositivity.KST.Comparison.IsHomotopyPullback`、`SerrePositivity.KST.Comparison.pullback_localized_isIso`

:::

:::corollary "kerodon_3_4_1_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_4_0_7, kerodon_3_4_0_9, kerodon_3_4_1_2")
Kerodon Corollary 3.4.1.6（[Tag 032E](https://kerodon.net/tag/032E)）。対応表の状態：なし。

B6：原文の指定 θ と置換模型の比較射を同一視する宣言が必要。 候補：一脚が Kan fibration のとき、厳密な引き戻しへの射の局所化同型性で判定できる。本文の Kan 底における区間模型への合成 θ に対する判定は未確認。

宣言：`SerrePositivity.KST.Comparison.isHomotopyPullback_iff_strict_of_left_fibration`、`SerrePositivity.KST.Comparison.IsHomotopyPullback`

:::

:::proposition "kerodon_3_4_1_9" (lean := "SerrePositivity.KST.Comparison.isHomotopyPullback_flip_iff")
Kerodon Proposition 3.4.1.9（[Tag 010Y](https://kerodon.net/tag/010Y)）。対応表の状態：本体にある。

仮定：任意の単体集合の可換正方形 sq（Kerodon と一致）。結論：IsHomotopyPullback sq.flip ↔ IsHomotopyPullback sq。二脚を入れ替えても性質が同じ（一致）。

:::

:::proposition "kerodon_3_4_1_11" (lean := "SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz, SerrePositivity.KST.Fibration.isHomotopyPullback_left_of_horiz")
Kerodon Proposition 3.4.1.11（[Tag 0110](https://kerodon.net/tag/0110)）。対応表の状態：本体にある。

仮定：横に並ぶ可換正方形で右が IsHomotopyPullback（Kerodon と一致）。結論：左もホモトピー引き戻しなら外周がそうなり、外周と右から左を逆に回収できる（一致）。

:::

:::corollary "kerodon_3_4_1_13" (uses := "kerodon_1_1_0_6, kerodon_3_4_1_5, kerodon_3_4_1_9, kerodon_3_4_1_11")
Kerodon Corollary 3.4.1.13（[Tag 0111](https://kerodon.net/tag/0111)）。対応表の状態：なし。

B6：四頂点とも弱同値の場合の保存/反映はあるが、原文のホモトピー引き戻しの区間模型との同定がなく、同じ正方形の結論とは未確認。 候補：四頂点の比較射が局所化同型ならホモトピー引き戻し性を保存・反映する。三頂点のみを仮定して残る頂点の弱同値を導く三条件のうち二つから三つ目、という形は未確認。

宣言：`SerrePositivity.KST.Comparison.isHomotopyPullback_iff_of_localized_isIso`、`SerrePositivity.KST.Comparison.homotopyPullbackComparison_naturality`

:::

:::proposition "kerodon_3_4_1_16" (uses := "kerodon_1_1_0_6, kerodon_3_4_1_11")
Kerodon Proposition 3.4.1.16（[Tag 01GN](https://kerodon.net/tag/01GN)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。simplicialSumReindex\_homotopyPullback\_of\_fibrations は各成分のホモトピー引き戻しを余積にまとめる。原文の一つの正方形から指定した直和因子を取り出す方向は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.4.2 Homotopy Pushout Squares

%%%
number := false
tag := "kerodon-3-4-2"
%%%

Kerodon [Tag 0112](https://kerodon.net/tag/0112)

:::definition "kerodon_3_4_2_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_4_1_1")
Kerodon Definition 3.4.2.1（[Tag 0113](https://kerodon.net/tag/0113)）。対応表の状態：なし。

B6：Bousfield–Kan cone の比較射の同値は、原文の区間模型で定義した任意の正方形の homotopy pullback 性との比較を欠く。 候補：任意の Kan 標的への内部 Hom の cospan の比較を、元の span が Kan 値かつ単射の脚を持つ場合に計算する。任意の正方形で全 Kan 標的へのホモトピー引き戻し性を要求する述語は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.underlyingPushoutHomCospanComparison_homotopyEquivalence`

:::

:::definition "kerodon_3_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder, SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse")
Kerodon Construction 3.4.2.2（[Tag 032K](https://kerodon.net/tag/032K)）。対応表の状態：一部。

B6：doubleMappingCylinder は区間の両端と二脚を貼る原文のホモトピー押し出しを直接構成し、collapse もその区間を潰す比較を与える。比較の Epi 性までは引用型にない。

:::

:::proposition "kerodon_3_4_2_5"
Kerodon Proposition 3.4.2.5（[Tag 032N](https://kerodon.net/tag/032N)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。二重写像円筒とその collapse、片脚が単射の collapse の弱同値性はある。任意の正方形を指定の二重写像円筒からの比較で判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_4_2_6"
Kerodon Proposition 3.4.2.6（[Tag 032P](https://kerodon.net/tag/032P)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合の op で弱可縮性を保つ補題はある。正方形全体に op を適用したときのホモトピー押し出し性の両方向は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_4_2_7"
Kerodon Proposition 3.4.2.7（[Tag 0114](https://kerodon.net/tag/0114)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。ホモトピー引き戻し性の flip 同値と通常の押し出しの対称性はある。任意の単体集合のホモトピー押し出し性の flip 同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_4_2_8"
Kerodon Proposition 3.4.2.8（[Tag 0115](https://kerodon.net/tag/0115)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の押し出しの貼り合わせとホモトピー引き戻しの貼り合わせはある。左のホモトピー押し出しから右と外周の同値を述べる双対の宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_4_2_9" (uses := "kerodon_1_1_0_6, kerodon_3_1_7_17, kerodon_3_4_1_13")
Kerodon Proposition 3.4.2.9（[Tag 0116](https://kerodon.net/tag/0116)）。対応表の状態：なし。

B6：二重写像円筒の比較の弱同値だけでは、原文の任意の終端頂点を含む三条件のいずれの含意も直接述べない。 候補：点ごとの弱同値から二重写像円筒間の弱同値を得る。任意の終端頂点を含む二つの正方形で、押し出し性と終端頂点の弱同値性を組み合わせた三条件は未確認。

宣言：`SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso`

:::

:::proposition "kerodon_3_4_2_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_17, kerodon_3_4_1_5")
Kerodon Proposition 3.4.2.10（[Tag 0117](https://kerodon.net/tag/0117)）。対応表の状態：なし。

B6：通常の押し出しの弱同値保存は原文の任意の正方形のホモトピー押し出し性との iff とは異なる。 候補：左固有性に当たる引用は通常の押し出しで一脚が単射などの条件下で局所化同型を保つ。任意の可換正方形について本文の iff を与えない。

宣言：`SerrePositivity.SimplicialModel.KanLocalizedLeftProper.localized_isIso`

:::

:::proposition "kerodon_3_4_2_11" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_3, kerodon_3_1_7_17")
Kerodon Proposition 3.4.2.11（[Tag 011A](https://kerodon.net/tag/011A)）。対応表の状態：なし。

B6：一般モデル圏の追加仮定を SSet で解消できず、通常pushoutを内部Homでpullbackに送る命題も原文のホモトピーpullbackとの比較が必要。 候補：仮定：Kerodon は単体集合の可換正方形で左上の脚が単射。候補の一般定理は \[ModelCategory C\]、局所可呈示性、cofibrantly generated と弱同値の cofibration に沿う押し出し安定性を要求する。具体的な C = SSet では ModelCategory の instance なし。結論：単体集合については Kan 複体の span の通常の押し出しの場合と、内部 Hom が押し出しを引き戻しに送ることを確認。任意の比較先に対する同値条件までは確認できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.underlyingPushoutHomCospanComparison_homotopyEquivalence`、`SerrePositivity.SimplicialModel.PushoutInternalHomPullback.isPullback`、`SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_span`

:::

:::corollary "kerodon_3_4_2_13" (lean := "SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse_localized_isIso")
Kerodon Corollary 3.4.2.13（[Tag 032Q](https://kerodon.net/tag/032Q)）。対応表の状態：一部。

B6：doubleMappingCylinderCollapse\_localized\_isIso は原文の指定の collapse が右脚 Mono のとき弱同値になる向きを直接与える。左脚だけ Mono の側は含まない。

:::

:::corollary "kerodon_3_4_2_14" (lean := "SerrePositivity.KST.Comparison.pushoutMap_localized_isIso")
Kerodon Corollary 3.4.2.14（[Tag 032R](https://kerodon.net/tag/032R)）。対応表の状態：本体にある。

仮定：二つの span のそれぞれに単射の指定脚があり、対応する三頂点の比較が弱ホモトピー同値（Kerodon と一致。Lean は脚の側を指定し、入れ替えは span の対称性で読む）。結論：通常の押し出しの誘導写像の局所化像は同型（一致）。

:::

:::corollary "kerodon_3_4_2_15" (lean := "SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso")
Kerodon Corollary 3.4.2.15（[Tag 032S](https://kerodon.net/tag/032S)）。対応表の状態：本体にある。

仮定：二つの単体集合の span と整合する三頂点の弱ホモトピー同値（Kerodon と一致。単射の条件は不要）。結論：二重写像円筒間の指定の比較が anodyne 局所化で同型で、同じ射が弱ホモトピー同値（一致）。

:::

:::proposition "kerodon_3_4_2_16"
Kerodon Proposition 3.4.2.16（[Tag 032T](https://kerodon.net/tag/032T)）。対応表の状態：なし。

B6：単体の解消のaugmentation と積への Quillen A は任意の二対象の引き戻し比較という同じ射を直接扱わない。 候補：各単体上での左ファイバーから固定した単体集合への比較と、単体ファイバーの図式の増大による解消はある。共通底への任意の二対象を、単体への引き戻し全体の比較で判定する型は未確認。

宣言：`SerrePositivity.KST.SConstruction.fiberResolutionAugmentation_localized_isIso`、`SerrePositivity.KST.SConstruction.simplicialProductQuillenA`

:::

:::corollary "kerodon_3_4_2_17" (lean := "SerrePositivity.KST.SConstruction.simplicialProductQuillenA")
Kerodon Corollary 3.4.2.17（[Tag 032U](https://kerodon.net/tag/032U)）。対応表の状態：一部。

B6：simplicialProductQuillenA で Z を終対象、g を終射に取ると仮定は各単体ファイバーの弱可縮性となり、結論は f の弱同値性（X→Y×1 を標準同型で同定）になる。同じ射への明示的な特殊化。

:::

# 3.4.3 Mather's Second Cube Theorem

%%%
number := false
tag := "kerodon-3-4-3"
%%%

Kerodon [Tag 011H](https://kerodon.net/tag/011H)

:::proposition "kerodon_3_4_3_2"
Kerodon Proposition 3.4.3.2（[Tag 011K](https://kerodon.net/tag/011K)）。対応表の状態：なし。

B6：通常の IsPushout の保存はホモトピー押し出し性の保存の証明部品で、同じ結論ではない。 候補：sliceFiberFunctor は厳密な押し出しを保存する。ホモトピー押し出し正方形を Kan fibration で基底変換する一般の型は未確認。

宣言：`SerrePositivity.KST.Comparison.sliceFiberFunctor_isPushout`

:::

:::theorem "kerodon_3_4_3_3"
Kerodon Theorem 3.4.3.3（[Tag 011M](https://kerodon.net/tag/011M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単射に沿う厳密な押し出しの van Kampen 性と、slice の引き戻しによる厳密押し出し保存はある。四面がホモトピー引き戻しという仮定で上面のホモトピー押し出しを得る第二立方体定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.4.4 Mather's First Cube Theorem

%%%
number := false
tag := "kerodon-3-4-4"
%%%

Kerodon [Tag 011Q](https://kerodon.net/tag/011Q)

:::proposition "kerodon_3_4_4_3" (lean := "SerrePositivity.KST.Comparison.spanPushout_vertex_homotopyPullback")
Kerodon Proposition 3.4.4.3（[Tag 011T](https://kerodon.net/tag/011T)）。対応表の状態：本体にある。

仮定：二つの span と、両方の脚の比較正方形がホモトピー引き戻しで、各 span の対応する脚が単射（Kerodon と一致）。結論：通常の押し出しへの比較と任意の span 頂点との自然性の正方形がホモトピー引き戻し（一致）。

:::

:::theorem "kerodon_3_4_4_4"
Kerodon Theorem 3.4.4.4（[Tag 011U](https://kerodon.net/tag/011U)）。対応表の状態：なし。

B6：厳密pushoutへの特殊化の候補はあるが、原文の区間模型のhomotopy pullbackとの比較を欠く。 候補：二重写像円筒での結果と、通常の押し出しで単射の脚がある場合は確認。任意のホモトピー押し出しを上下に指定した立方体で二面を回収する一般の型は未確認。

宣言：`SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback`、`SerrePositivity.KST.Comparison.spanPushout_vertex_homotopyPullback`

:::

# 3.4.5 Digression: Weak Homotopy Equivalences of Semisimplicial Sets

%%%
number := false
tag := "kerodon-3-4-5"
%%%

Kerodon [Tag 0120](https://kerodon.net/tag/0120)

:::definition "kerodon_3_4_5_1" (uses := "kerodon_1_1_0_6, kerodon_3_1_7_12")
Kerodon Definition 3.4.5.1（[Tag 0121](https://kerodon.net/tag/0121)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。freeDegeneracies は既存の単体集合の次数を使う。任意の半単体集合の写像の弱同値を自由退化により定義する述語は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_4_5_4" (lean := "SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso, SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation")
Kerodon Proposition 3.4.5.4（[Tag 0124](https://kerodon.net/tag/0124)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：自由退化模型から X への augmentation が anodyne 局所化で同型。これは同じ augmentation が弱ホモトピー同値という主張（一致）。

:::

:::corollary "kerodon_3_4_5_5" (uses := "kerodon_1_1_0_6, kerodon_3_1_7_12, kerodon_3_4_5_1, kerodon_3_4_5_4")
Kerodon Corollary 3.4.5.5（[Tag 0125](https://kerodon.net/tag/0125)）。対応表の状態：なし。

B6：augmentation の弱同値性は写像 f での半単体弱同値との iff ではなく、その比較の部品。 候補：元の単体集合について自由退化の augmentation が弱同値であることを確認。忘却した半単体集合の弱同値述語との iff は未確認。

宣言：`SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso`

:::

:::corollary "kerodon_3_4_5_6"
Kerodon Corollary 3.4.5.6（[Tag 0126](https://kerodon.net/tag/0126)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。自由退化の既存の比較は X⁺→X。半単体集合 X から X⁺ への包含が半単体集合の弱同値になる宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_4_5_7" (uses := "kerodon_1_1_0_6, kerodon_3_3_5_2, kerodon_3_4_5_4, kerodon_3_4_5_5")
Kerodon Variant 3.4.5.7（[Tag 0127](https://kerodon.net/tag/0127)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合での freeDegeneracies と Ex の別々の構成はある。半単体の包含に Ex をかけた指定射の弱同値性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_4_5_8" (uses := "kerodon_1_1_0_6, kerodon_3_3_5_2, kerodon_3_4_5_5, kerodon_3_4_5_7")
Kerodon Corollary 3.4.5.8（[Tag 0128](https://kerodon.net/tag/0128)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Ex∞ の単体集合の弱同値保存・反映はある。半単体写像と一段の Ex の間の弱同値の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_4_5_9" (uses := "kerodon_1_1_0_6, kerodon_3_3_1_11")
Kerodon Lemma 3.4.5.9（[Tag 0129](https://kerodon.net/tag/0129)）。対応表の状態：なし。

B6：弱同値という候補の結論から、Kan と限らない nerve のホモトピー逆は得ない。 候補：任意の単体集合の freeDegeneraciesAugmentation の弱ホモトピー同値性は確認。非恒等射の合成条件を持つ普通圏の nerve で、実ホモトピー逆まで得る強化は未確認。

宣言：`SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso`

:::

# 3.4.6 Excision

%%%
number := false
tag := "kerodon-3-4-6"
%%%

Kerodon [Tag 012B](https://kerodon.net/tag/012B)

:::theorem "kerodon_3_4_6_1" (uses := "kerodon_1_1_0_6, kerodon_3_4_2_1, kerodon_3_4_6_6")
Kerodon Theorem 3.4.6.1（[Tag 012C](https://kerodon.net/tag/012C)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合の相対整数ホモロジーと単射に沿う押し出しはある。位相空間の内部被覆を入力して特異単体集合のホモトピー押し出しを得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_4_6_4"
Kerodon Definition 3.4.6.4（[Tag 012F](https://kerodon.net/tag/012F)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。特異単体集合の関手はある。各単体が被覆族の一つの部分空間に入るという条件で定める部分複体は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::theorem "kerodon_3_4_6_6" (uses := "kerodon_1_1_0_6, kerodon_3_3_2_3, kerodon_3_3_2_10, kerodon_3_3_4_3, kerodon_3_3_5_1, kerodon_3_4_5_5, kerodon_3_4_5_8, kerodon_3_4_6_7")
Kerodon Theorem 3.4.6.6（[Tag 012H](https://kerodon.net/tag/012H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体の細分と一般の弱同値の比較はある。被覆に従属する特異小単体の部分複体の包含が弱同値という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_4_6_7" (uses := "kerodon_3_3_2_3")
Kerodon Lemma 3.4.6.7（[Tag 012J](https://kerodon.net/tag/012J)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。凸包と直径の一般 API はある。重心細分の一単体の像について n/(n+1) の係数で直径を抑える型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.4.7 The Seifert van-Kampen Theorem

%%%
number := false
tag := "kerodon-3-4-7"
%%%

Kerodon [Tag 012K](https://kerodon.net/tag/012K)

:::theorem "kerodon_3_4_7_1"
Kerodon Theorem 3.4.7.1（[Tag 012L](https://kerodon.net/tag/012L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Mathlib の基本群と普通の群の押し出しの API はある。交わり・両側・全体の基本群の指定正方形を押し出しとする位相的 van Kampen 定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::theorem "kerodon_3_4_7_2"
Kerodon Theorem 3.4.7.2（[Tag 012M](https://kerodon.net/tag/012M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。基本亜群と圏の押し出しの API はある。位相空間の被覆に対して基本亜群の指定の押し出しを与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::theorem "kerodon_3_4_7_3"
Kerodon Theorem 3.4.7.3（[Tag 012N](https://kerodon.net/tag/012N)）。対応表の状態：なし。

B6：単体集合のpushoutでの結果は位相的被覆の特異鎖へのexcisionの結論ではない。 候補：単体集合の厳密な押し出しから整数ホモロジー同型を得る補題はある。位相的被覆の特異鎖を入力して相対ホモロジー同型を結論する excision は未確認。

宣言：`SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_pushout`

:::

