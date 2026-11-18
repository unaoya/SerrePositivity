import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianCancellation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCancellation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "5.1 Cartesian Fibrations" =>
%%%
number := false
tag := "kerodon-5-1"
%%%

Kerodon の 5.1 節（[Tag 01T1](https://kerodon.net/tag/01T1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.1.1 Cartesian Edges of Simplicial Sets

%%%
number := false
tag := "kerodon-5-1-1"
%%%

Kerodon [Tag 01T4](https://kerodon.net/tag/01T4)

:::definition "kerodon_5_1_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting")
Kerodon Definition 5.1.1.1（[Tag 01T5](https://kerodon.net/tag/01T5)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 q:X→S と X の 1 単体 e（Kerodon と一致）。結論：cartesian は終辺 e を固定した最後の外ホーンの持ち上げ性、cocartesian は初辺 e を固定した最初の外ホーンの持ち上げ性（一致）。

:::

:::proposition "kerodon_5_1_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_iff_isInvertibleEdge_of_map, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge")
Kerodon Example 5.1.1.4（[Tag 01T8](https://kerodon.net/tag/01T8)）。対応表の状態：本体にある。

仮定：∞ 圏 X から点への射と辺 e（Lean が弱い：像が可逆な一般の内ファイブレーションにも適用）。結論：e の可逆性、cartesian 性、cocartesian 性が同値。点への像は恒等辺（一致）。

:::

:::proposition "kerodon_5_1_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCocartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge")
Kerodon Proposition 5.1.1.9（[Tag 01TB](https://kerodon.net/tag/01TB)）。対応表の状態：本体にある。

仮定：∞ 圏間の内ファイブレーション p と始域の辺 e（Kerodon と一致）。結論：e の可逆性は cartesian 性かつ像の可逆性と同値。cocartesian 側にも同じ同値（一致）。

:::

:::corollary "kerodon_5_1_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_constant, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge")
Kerodon Corollary 5.1.1.10（[Tag 01TC](https://kerodon.net/tag/01TC)）。対応表の状態：本体にある。

仮定：∞ 圏間の内ファイブレーション p と頂点 x（Kerodon と一致）。結論：定値 1 単体 id\_x が cocartesian。id\_x の可逆性から cartesian でもある（一致）。

:::

:::corollary "kerodon_5_1_1_11" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_5_1_1_9")
Kerodon Corollary 5.1.1.11（[Tag 023H](https://kerodon.net/tag/023H)）。対応表の状態：一部。

底がKanなので像の全辺は可逆。isInvertibleEdge\_iff\_isCartesianEdgeは原文の(1)⇔(2)を同じ辺について直接与える。(3)との同値は引用した型だけにはない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge`

:::

:::proposition "kerodon_5_1_1_14" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_16")
Kerodon Proposition 5.1.1.14（[Tag 01TF](https://kerodon.net/tag/01TF)）。対応表の状態：一部。

isCocartesianEdge\_iff\_relativeCosliceMap\_trivialKanFibrationは原文後半の同じ相対coslice比較のiff。cartesian/slice側は別なので含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge`

:::

:::corollary "kerodon_5_1_1_15" (uses := "kerodon_1_1_0_6, kerodon_4_3_7_17, kerodon_5_1_1_14")
Kerodon Corollary 5.1.1.15（[Tag 01TG](https://kerodon.net/tag/01TG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と元の辺・双対の slice・普通の fibered categoryを照合。coslice の辺の q′-cartesian 性を元の辺で判定する結果。通常の pullback での保存では coslice の join 制約を扱わない。

:::

:::corollary "kerodon_5_1_1_16" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_14")
Kerodon Corollary 5.1.1.16（[Tag 01TH](https://kerodon.net/tag/01TH)）。対応表の状態：なし。

引用はcocartesian辺eの始点へのcoslice制限であり、原文のcartesian辺eと任意A⊆Bの相対cosliceの終点持ち上げの判定ではない。双対で別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_source_of_isCocartesianEdge`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_relativeCosliceRestriction_source`

:::

# 5.1.2 Cartesian Morphisms of ∞-Categories

%%%
number := false
tag := "kerodon-5-1-2"
%%%

Kerodon [Tag 01TK](https://kerodon.net/tag/01TK)

:::proposition "kerodon_5_1_2_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_6, kerodon_3_4_1_13, kerodon_4_3_6_8, kerodon_4_3_6_12, kerodon_4_3_6_14, kerodon_4_4_2_14, kerodon_4_4_3_8, kerodon_4_6_5_7, kerodon_4_6_5_10, kerodon_4_6_8_5, kerodon_5_1_1_14")
Kerodon Proposition 5.1.2.1（[Tag 01TL](https://kerodon.net/tag/01TL)）。対応表の状態：なし。

IsStronglyCartesianは通常圏のHom集合の普遍性。原文の準圏の指定Kan写像空間の四角への比較がなく、同じ射のホモトピーpullback判定を直接与えない。

宣言：`CategoryTheory.Functor.IsStronglyCartesian`

:::

:::corollary "kerodon_5_1_2_2"
Kerodon Corollary 5.1.2.2（[Tag 01TN](https://kerodon.net/tag/01TN)）。対応表の状態：なし。

IsStronglyCartesianの通常圏の定義は、原文の脈体のcartesian辺とのiffの片側ではない。nerve比較をする宣言を欠く。

宣言：`CategoryTheory.Functor.IsStronglyCartesian`

:::

:::corollary "kerodon_5_1_2_3" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_6_8_5, kerodon_4_6_8_15, kerodon_5_1_2_1")
Kerodon Corollary 5.1.2.3（[Tag 01TQ](https://kerodon.net/tag/01TQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Hom の引き戻し・薄い底の場合・写像空間の比較を照合。半順序の nerve 上で、各 X の写像空間に対する合成が hKan で同型となる cartesian 辺の判定。薄い nerve の inner 性と区別した。

:::

:::corollary "kerodon_5_1_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_second_of_first_long, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long")
Kerodon Corollary 5.1.2.4（[Tag 01TS](https://kerodon.net/tag/01TS)）。対応表の状態：本体にある。

仮定：∞ 圏間の内ファイブレーション q と 2 単体 (f,g,h)（Lean が弱い：始域の ∞ 圏性を明示しない）。結論：g が cartesian なら f と h の cartesian 性が同値。f が cocartesian なら g と h の cocartesian 性が同値（一致）。

:::

:::corollary "kerodon_5_1_2_5" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_9, kerodon_5_1_2_4")
Kerodon Corollary 5.1.2.5（[Tag 01TT](https://kerodon.net/tag/01TT)）。対応表の状態：一部。

A=Δ¹、eを非退化辺とするとisCocartesianEdge\_iff\_of\_functorIsoは原文後半の同じFun(Δ¹,C)内同型でのcocartesian性のiffを直接与える。cartesian側は含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_of_functorIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_functorIso`

:::

:::corollary "kerodon_5_1_2_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_11, kerodon_5_1_1_1, kerodon_5_1_2_1")
Kerodon Corollary 5.1.2.6（[Tag 01TU](https://kerodon.net/tag/01TU)）。対応表の状態：一部。

IsCartesianEdge.compはp-cartesianかつ像がq-cartesianから合成に対しcartesianというiffの順方向を直接返す。逆方向は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge.comp`

:::

# 5.1.3 Locally Cartesian Edges

%%%
number := false
tag := "kerodon-5-1-3"
%%%

Kerodon [Tag 01TW](https://kerodon.net/tag/01TW)

:::definition "kerodon_5_1_3_1"
Kerodon Definition 5.1.3.1（[Tag 01TX](https://kerodon.net/tag/01TX)）。対応表の状態：なし。

Mathlibの弱いIsCartesian/IsCocartesianと、底の辺Δ¹への引き戻し後のcartesian辺を比較する型がない。通常圏の類似の定義だけでは数えない。

宣言：`CategoryTheory.Functor.IsCartesian`、`CategoryTheory.Functor.IsCocartesian`

:::

:::proposition "kerodon_5_1_3_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_2_4")
Kerodon Proposition 5.1.3.7（[Tag 01U4](https://kerodon.net/tag/01U4)）。対応表の状態：なし。

引用は大域的なcartesian辺の三角形の取消し。原文の局所cartesian性との比較がなく、gが大域的という仮定だけから同じ局所iffを直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long`

:::

:::corollary "kerodon_5_1_3_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_2_4")
Kerodon Corollary 5.1.3.9（[Tag 01U6](https://kerodon.net/tag/01U6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：区間 Δ¹ の持ち上げ・一方が大域的な三角形・ファイバー写像空間を照合。指定した底辺と終点に大域 cartesian な持ち上げがあるとき、局所 cartesian な別の持ち上げも大域的となる結論。通常の持ち上げの一意性だけでは局所性から始められない。

:::

:::definition "kerodon_5_1_3_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_1_16, kerodon_4_6_8_1, kerodon_4_6_8_4")
Kerodon Notation 5.1.3.10（[Tag 01U7](https://kerodon.net/tag/01U7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：区間 Δ¹ の持ち上げ・一方が大域的な三角形・ファイバー写像空間を照合。底の辺を固定した局所 cartesian の写像空間判定。単一ファイバー上の pinched Hom の同型は合成による比較射を与えない。

:::

:::proposition "kerodon_5_1_3_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_2_3, kerodon_5_1_3_10")
Kerodon Proposition 5.1.3.11（[Tag 01U8](https://kerodon.net/tag/01U8)）。対応表の状態：なし。

引用は区間上のcocartesian辺を保つ二つの図式のcoslice写像間の同値の輸送。原文の一つの局所cartesian辺の合成作用の判定とは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_source_equivalence_of_target`

:::

# 5.1.4 Cartesian Fibrations

%%%
number := false
tag := "kerodon-5-1-4"
%%%

Kerodon [Tag 01U9](https://kerodon.net/tag/01U9)

:::definition "kerodon_5_1_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibrations, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration")
Kerodon Definition 5.1.4.1（[Tag 01UA](https://kerodon.net/tag/01UA)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 p（Kerodon と一致）。結論：内ファイブレーションで、各底の辺を指定終点から cartesian に、または指定始点から cocartesian に持ち上げられる（一致）。

:::

:::proposition "kerodon_5_1_4_8" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.8（[Tag 023J](https://kerodon.net/tag/023J)）。対応表の状態：一部。

cartesianFibration\_pullback\_sndに各σ:Δⁿ→Sを代入すれば原文の順方向そのもの。全ての単体上から大域性を回収する逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd`

:::

:::proposition "kerodon_5_1_4_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.9（[Tag 01UG](https://kerodon.net/tag/01UG)）。対応表の状態：なし。

引用はcocartesian fibrationのequivalence lifting。原文のcartesian fibrationからisofibrationという主張とは向きが異なり、反転でisofibrationを輸送する比較を引用型は与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanInvertibleTargetLifting`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting`

:::

:::corollary "kerodon_5_1_4_11"
Kerodon Corollary 5.1.4.11（[Tag 023K](https://kerodon.net/tag/023K)）。対応表の状態：一部。

底Kanは準圏で、cocartesianFibration\_kanEquivalenceLiftingとisofibrationの二条件のiffにより原文(3)⇒(1)が直接得られる。三条件全体の同値ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting`、`SSet.quasicategory_of_innerFibration`

:::

:::proposition "kerodon_5_1_4_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.12（[Tag 01UJ](https://kerodon.net/tag/01UJ)）。対応表の状態：なし。

引用はcocartesianなhorn liftingと全空間Eでの可逆性のiff。原文はcartesian辺と退化辺上の厳密fiber内での可逆性であり、fiber包含との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_iff_isInvertibleEdge_of_map`

:::

:::proposition "kerodon_5_1_4_13" (uses := "kerodon_1_1_0_6, kerodon_5_1_3_7, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.13（[Tag 01UK](https://kerodon.net/tag/01UK)）。対応表の状態：一部。

底Sを準圏に強めると現本体のisCartesianEdge\_triangle\_longEdgeとisCartesianEdge\_triangle\_first\_of\_second\_longを同じσとgに適用し、原文のfがcartesian iff hがcartesianを直接得る。一般の単体集合の底ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long`

:::

:::proposition "kerodon_5_1_4_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.14（[Tag 01UL](https://kerodon.net/tag/01UL)）。対応表の状態：一部。

cartesianFibration\_compは原文の合成のcartesian fibration性、IsCartesianEdge.compは辺の判定の十分条件を直接与える。辺の必要条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_comp`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_comp`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp`

:::

:::proposition "kerodon_5_1_4_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_4_4_2_1, kerodon_5_1_1_1, kerodon_5_1_3_9, kerodon_5_1_4_1, kerodon_5_1_4_12")
Kerodon Proposition 5.1.4.15（[Tag 01UM](https://kerodon.net/tag/01UM)）。対応表の状態：一部。

rightFibration\_iff\_cartesianFibration\_all\_edgesは同じqについて原文(1)⇔(2)そのもの。(3)の全fiber Kanとの同値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_iff_cocartesianFibration_all_edges`

:::

:::corollary "kerodon_5_1_4_16" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_13")
Kerodon Corollary 5.1.4.16（[Tag 01UN](https://kerodon.net/tag/01UN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。全辺が q-cartesian な単体で張る部分複体が右ファイブレーションとなる主張。通常の quasicategory core は可逆辺で張る。

:::

:::proposition "kerodon_5_1_4_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_2_15, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.17（[Tag 02R5](https://kerodon.net/tag/02R5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。充満部分複体で cartesian lift の始点を選べる場合の制限と辺の判定。任意の底変換とは全空間の部分複体に沿う点が異なる。

:::

:::proposition "kerodon_5_1_4_18"
Kerodon Proposition 5.1.4.18（[Tag 01UP](https://kerodon.net/tag/01UP)）。対応表の状態：一部。

qをtrivial Kan fibrationに強めればsliceOverPostcomp\_trivialKanFibrationは原文(1)の同じslice後合成がtrivial Kan、従ってcartesian fibrationと直接与える。一般のqと(2)は含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp_trivialKanFibration`

:::

:::lemma_ "kerodon_5_1_4_19" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_10, kerodon_5_1_1_15, kerodon_5_1_2_6")
Kerodon Lemma 5.1.4.19（[Tag 01UQ](https://kerodon.net/tag/01UQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。coslice の制限比較で、像の辺が q-cartesian なら比較射に対しても cartesian となる主張。単なる coslice 制限の内ファイブレーション性では辺ごとの条件が出ない。

:::

:::proposition "kerodon_5_1_4_20" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_8, kerodon_5_1_1_1, kerodon_5_1_1_16, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13, kerodon_5_1_4_19")
Kerodon Proposition 5.1.4.20（[Tag 01UR](https://kerodon.net/tag/01UR)）。対応表の状態：一部。

qをtrivial Kan fibrationに強めればtrivialKanFibration\_sliceUnderPostcompは原文(1)の同じcoslice後合成がtrivial Kan、従ってcartesian fibrationと直接与える。一般のqと(2)は含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceUnderPostcomp`

:::

:::proposition "kerodon_5_1_4_21" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_6, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.21（[Tag 02VV](https://kerodon.net/tag/02VV)）。対応表の状態：一部。

全空間と底を準圏、F₀をinner fibration、各fiber上のF₀にもinvertible target liftingを追加するとcartesianFibration\_pullback\_overは原文と同じ合成射のcartesian fibration性を直接与える。辺の必要条件と元のF₁だけの仮定への一般化は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_over`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback_over`

:::

:::corollary "kerodon_5_1_4_22" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_20, kerodon_5_1_4_21")
Kerodon Corollary 5.1.4.22（[Tag 03LL](https://kerodon.net/tag/03LL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。cartesian 辺を保つ底上の射と f の coslice を組み合わせた pullback 比較の cartesian 性。pullback.snd の閉性の型では比較射が異なる。

:::

# 5.1.5 Locally Cartesian Fibrations

%%%
number := false
tag := "kerodon-5-1-5"
%%%

Kerodon [Tag 01UW](https://kerodon.net/tag/01UW)

:::definition "kerodon_5_1_5_1"
Kerodon Definition 5.1.5.1（[Tag 01UX](https://kerodon.net/tag/01UX)）。対応表の状態：なし。

IsPreFiberedは通常圏での弱いcartesian持ち上げ。原文の単体集合のinner fibrationとΔ¹に制限した局所cartesian辺の条件への比較がない。

宣言：`CategoryTheory.Functor.IsPreFibered`

:::

:::proposition "kerodon_5_1_5_9"
Kerodon Proposition 5.1.5.9（[Tag 01V5](https://kerodon.net/tag/01V5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian な fibration で、任意の三角形の辺の条件から個々の辺の大域 cartesian 性を判定。合成・取消しの型は最初から大域的な辺を使う。

:::

:::corollary "kerodon_5_1_5_10"
Kerodon Corollary 5.1.5.10（[Tag 01V6](https://kerodon.net/tag/01V6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の大域化と、局所 cartesian 辺が三角形で合成に閉じることの同値。大域的な合成補題と区別した。

:::

:::corollary "kerodon_5_1_5_11"
Kerodon Corollary 5.1.5.11（[Tag 01V7](https://kerodon.net/tag/01V7)）。対応表の状態：一部。

cartesianFibration\_pullback\_sndはn≤2の全σにも直接適用でき、原文の順方向を与える。低次元だけからの逆判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd`

:::

:::corollary "kerodon_5_1_5_12"
Kerodon Corollary 5.1.5.12（[Tag 046V](https://kerodon.net/tag/046V)）。対応表の状態：一部。

qを大域cartesian fibrationに強めるとrightFibration\_iff\_cartesianFibration\_all\_edgesは原文(1)⇔(4)を直接返す。locallyの定義と(2),(3)の同値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges`

:::

:::proposition "kerodon_5_1_5_13"
Kerodon Proposition 5.1.5.13（[Tag 01V8](https://kerodon.net/tag/01V8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration を図式に沿う slice 比較に移し、局所 cartesian 辺を同定する主張。slice 内ファイブレーションの型だけでは局所性の判定がない。

:::

:::proposition "kerodon_5_1_5_14" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_9_8_1, kerodon_4_9_8_7, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1")
Kerodon Proposition 5.1.5.14（[Tag 047P](https://kerodon.net/tag/047P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の局所 κ-small 性と各頂点ファイバーの局所 κ-small 性の同値。ファイバーの ∞ 圏性に濃度はない。

:::

:::corollary "kerodon_5_1_5_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_5_5, kerodon_5_1_4_1, kerodon_5_1_5_14")
Kerodon Corollary 5.1.5.15（[Tag 047Q](https://kerodon.net/tag/047Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の本質的 κ-small 性を全頂点ファイバーで判定。universe lift の型に任意の非可算 κ はない。

:::

:::corollary "kerodon_5_1_5_16" (uses := "kerodon_1_4_0_1, kerodon_4_9_8_12, kerodon_5_1_5_15")
Kerodon Corollary 5.1.5.16（[Tag 05DV](https://kerodon.net/tag/05DV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。非可算正則 κ の下で、局所 cartesian isofibration の全空間と各ファイバーの本質的 κ-small 性を比較。ファイバーごとの同値判定は濃度評価ではない。

:::

:::definition "kerodon_5_1_5_17"
Kerodon Variant 5.1.5.17（[Tag 05DW](https://kerodon.net/tag/05DW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の n-faithful 性とファイバーの局所 (n−2)-truncation の比較。full faithfulness とファイバーの可縮性だけでは次数一般を扱わない。

:::

:::corollary "kerodon_5_1_5_18"
Kerodon Corollary 5.1.5.18（[Tag 05DX](https://kerodon.net/tag/05DX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。右ファイブレーションの n-faithful 性と各ファイバーの (n−1)-truncation の同値。right fibration の Kan ファイバー補題は任意次数を判定しない。

:::

:::proposition "kerodon_5_1_5_19"
Kerodon Proposition 5.1.5.19（[Tag 01V9](https://kerodon.net/tag/01V9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian な二射の四角で、各ファイバーでの局所 cartesian 条件を使う比較。通常の pullback の cartesian 性とは四角の仮定が違う。

:::

# 5.1.6 Fiberwise Equivalence

%%%
number := false
tag := "kerodon-5-1-6"
%%%

Kerodon [Tag 023L](https://kerodon.net/tag/023L)

:::theorem "kerodon_5_1_6_1" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_9, kerodon_4_5_3_31, kerodon_4_8_4_1, kerodon_5_1_1_1, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_5_1_6_6, kerodon_5_1_6_7")
Kerodon Theorem 5.1.6.1（[Tag 023M](https://kerodon.net/tag/023M)）。対応表の状態：一部。

底射を恒等、両縦射をKan fibrationに制限すればleft fibrationでもあり、isQCatEquivalence\_of\_leftFibration\_fibersは同じ全空間射Fの同値をfiberの同値から直接与える。一般cartesian版やiff全体ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_of_vertexFiberMap`

:::

:::corollary "kerodon_5_1_6_2" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_8, kerodon_5_1_4_1, kerodon_5_1_6_1")
Kerodon Corollary 5.1.6.2（[Tag 023N](https://kerodon.net/tag/023N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。両縦が isofibration、両横が ∞ 圏同値の四角で cartesian と cocartesian をそれぞれ移す結果。同型な全空間間の辺の保存より広い。

:::

:::corollary "kerodon_5_1_6_3"
Kerodon Corollary 5.1.6.3（[Tag 023P](https://kerodon.net/tag/023P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。isofibration の四角で両横の ∞ 圏同値から右・左ファイブレーション性を保存・反映。反対圏で左右を交換する定理はこの四角を扱わない。

:::

:::corollary "kerodon_5_1_6_4" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Corollary 5.1.6.4（[Tag 01VE](https://kerodon.net/tag/01VE)）。対応表の状態：一部。

同じ底上のKan fibration間に制限すれば両縦射はleft/right fibration。leftFibration\_isQCatEquivalence\_iff\_fibersは同じFと同じKan fiberの同値のiffを直接返す。rightのみ・底を変える一般の場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_precompositionEquivalence_iff_fibers`

:::

:::lemma_ "kerodon_5_1_6_5" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_5_1_1_1, kerodon_5_1_2_1")
Kerodon Lemma 5.1.6.5（[Tag 023Q](https://kerodon.net/tag/023Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。内ファイブレーションの四角で、充満忠実性を使い像辺から元の cartesian 性を反映する結果。通常圏の strongly cartesian の型とは入力が異なる。

:::

:::proposition "kerodon_5_1_6_6" (uses := "kerodon_1_4_0_1, kerodon_5_1_2_5, kerodon_5_1_6_2, kerodon_5_1_6_5")
Kerodon Proposition 5.1.6.6（[Tag 023R](https://kerodon.net/tag/023R)）。対応表の状態：なし。

引用は同じpの下でFunctorIsoによってcocartesian辺を移す型。原文の二つのisofibrationと上下の圏同値に沿うcartesian性の移送とは別の図式。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_of_functorIso`

:::

:::proposition "kerodon_5_1_6_7" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_8_1, kerodon_4_6_1_22, kerodon_4_8_3_39, kerodon_5_1_1_1, kerodon_5_1_3_10, kerodon_5_1_3_11, kerodon_5_1_4_1")
Kerodon Proposition 5.1.6.7（[Tag 01VB](https://kerodon.net/tag/01VB)）。対応表の状態：なし。

引用は区間上のcocartesian liftに基づく充満忠実性。原文のcartesian lift・任意の充満忠実な底射・局所cartesian性と同じ条件を直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesian_crossing_mapping_equivalence_of_target`

:::

# 5.1.7 Equivalence of Inner Fibrations

%%%
number := false
tag := "kerodon-5-1-7"
%%%

Kerodon [Tag 0280](https://kerodon.net/tag/0280)

:::definition "kerodon_5_1_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 5.1.7.1（[Tag 0281](https://kerodon.net/tag/0281)）。対応表の状態：一部。

left fibrationと準圏の底に制限しFが前合成同値なら、exists\_relativeFunctorInverse\_of\_precompositionEquivalenceは底上の逆射と二つの相対Functor空間での同型を直接構成する。原文の相対逆の構成成分で、任意inner fibrationの述語全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

:::proposition "kerodon_5_1_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_5_10, kerodon_4_5_5_11")
Kerodon Proposition 5.1.7.5（[Tag 0285](https://kerodon.net/tag/0285)）。対応表の状態：一部。

底を準圏、U,Vをleft fibrationに強め、Fの前合成同値を仮定するとexists\_relativeFunctorInverse\_of\_precompositionEquivalenceが原文(2)の底上の相対逆と相対単位・余単位を直接返す。一般isofibrationへの拡張と(1)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

:::corollary "kerodon_5_1_7_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_7_5")
Kerodon Corollary 5.1.7.8（[Tag 0287](https://kerodon.net/tag/0287)）。対応表の状態：なし。

引用のiffの右辺は頂点fiberの同値であり、原文の左辺の底上の相対逆の存在ではない。全空間同値とfiber同値の比較だけを原文の相対逆のiffとして数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`

:::

:::proposition "kerodon_5_1_7_9" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_1, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_8_1, kerodon_4_4_3_7, kerodon_4_4_5_1, kerodon_4_5_3_31, kerodon_4_5_7_23, kerodon_4_8_4_6, kerodon_5_1_7_8")
Kerodon Proposition 5.1.7.9（[Tag 0288](https://kerodon.net/tag/0288)）。対応表の状態：一部。

底準圏・両縦left fibrationに制限すると、原文(4)は特に全頂点fiberの同値を含む。relativeFunctorPost\_isQCatEquivalence\_on\_baseに恒等底射を代入すれば同じ相対Functor後合成の同値(2)を直接返す。全四条件のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_on_base`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialSectionsMap_homotopyEquivalence_of_fibers`

:::

:::corollary "kerodon_5_1_7_10"
Kerodon Corollary 5.1.7.10（[Tag 05J4](https://kerodon.net/tag/05J4)）。対応表の状態：なし。

引用の結論は全空間Fの本質的全射性・圏同値。原文が判定するのは底上の相対逆の存在で、同値から相対逆へ進む比較が引用型にない。証明の部品だけを数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_of_vertexFiberMap_equivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`

:::

:::proposition "kerodon_5_1_7_11" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_3_33, kerodon_5_1_7_1, kerodon_5_1_7_8, kerodon_5_1_7_9")
Kerodon Proposition 5.1.7.11（[Tag 028E](https://kerodon.net/tag/028E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：left fibration の場合・Δ¹・各ファイバーの場合・相対同値と引き戻しを照合。同型な F,G に沿う isofibration の二つの引き戻しの底 C 上の比較。通常の pullback が変数の厳密な同型を保つ型では、∞ 圏の Fun 内の同型を扱わない。

:::

:::lemma_ "kerodon_5_1_7_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_9, kerodon_4_4_5_8, kerodon_5_1_7_5")
Kerodon Lemma 5.1.7.13（[Tag 0289](https://kerodon.net/tag/0289)）。対応表の状態：なし。

引用の相対逆は二つの合成と恒等の同型のみ。原文(2)が指定するG∘F=idの厳密等式とF上で恒等になる相対同型の正規化を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

:::proposition "kerodon_5_1_7_14" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_4_8, kerodon_5_1_4_15, kerodon_5_1_6_2, kerodon_5_1_7_8, kerodon_5_1_7_13")
Kerodon Proposition 5.1.7.14（[Tag 028A](https://kerodon.net/tag/028A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：left fibration の場合・Δ¹・各ファイバーの場合・相対同値と引き戻しを照合。底上で同値な二つの内ファイブレーション間で各種 fibration・covering の性質を比較する結果。op による左右交換はこの相対同値と異なる。

:::

:::proposition "kerodon_5_1_7_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_1_7_8, kerodon_5_1_7_9")
Kerodon Proposition 5.1.7.15（[Tag 028B](https://kerodon.net/tag/028B)）。対応表の状態：なし。

引用はleft fibrationの全空間同値とfiber同値のiff。原文のcartesian fibrationの相対逆とcartesian辺保存の判定とは、射の型・比較対象が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`

:::

:::corollary "kerodon_5_1_7_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_1_4_15, kerodon_5_1_7_15")
Kerodon Corollary 5.1.7.16（[Tag 028C](https://kerodon.net/tag/028C)）。対応表の状態：なし。

引用はleft fibrationの前合成同値と相対逆。right fibrationの同じ射への反転と相対Functor空間の比較が型にないため、双対の類似だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_precompositionEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

