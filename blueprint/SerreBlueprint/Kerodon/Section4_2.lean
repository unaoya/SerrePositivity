import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.FirstVertexLeftAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.2 Left and Right Fibrations" =>
%%%
number := false
tag := "kerodon-4-2"
%%%

Kerodon の 4.2 節（[Tag 014H](https://kerodon.net/tag/014H)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.2.1 Left and Right Fibrations of Simplicial Sets

%%%
number := false
tag := "kerodon-4-2-1"
%%%

Kerodon [Tag 01GT](https://kerodon.net/tag/01GT)

:::definition "kerodon_4_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations")
Kerodon Definition 4.2.1.1（[Tag 00T9](https://kerodon.net/tag/00T9)）。対応表の状態：本体にある。

仮定：単体集合間の任意の射 f（Kerodon と一致）。結論：LeftFibration は 0≤i\<n、RightFibration は 0\<i≤n のホーンに対する右持ち上げ性（一致）。

:::

# 4.2.2 Fibrations in Groupoids

%%%
number := false
tag := "kerodon-4-2-2"
%%%

Kerodon [Tag 0156](https://kerodon.net/tag/0156)

:::definition "kerodon_4_2_2_1"
Kerodon Definition 4.2.2.1（[Tag 0157](https://kerodon.net/tag/0157)）。対応表の状態：一部。

IsFibered の cartesian lift の存在から原文(A)の任意の底の射の持ち上げが直接得られる。全ての射についてのHomのpullback条件(B)は含まない。

宣言：`CategoryTheory.Functor.IsFibered`、`CategoryTheory.Functor.IsStronglyCartesian`

:::

:::definition "kerodon_4_2_2_4"
Kerodon Variant 4.2.2.4（[Tag 015A](https://kerodon.net/tag/015A)）。対応表の状態：なし。

IsStronglyCocartesian は選んだ一つの射についての普遍性。原文の任意の底の射の持ち上げの存在も、全ての射に対するpullback条件もこの型だけでは返さない。

宣言：`CategoryTheory.Functor.IsStronglyCocartesian`

:::

:::proposition "kerodon_4_2_2_9"
Kerodon Proposition 4.2.2.9（[Tag 015H](https://kerodon.net/tag/015H)）。対応表の状態：一部。

costructuredArrowProjection\_rightFibration は U=CostructuredArrow.proj Q V の同じ nerveMap U の right fibration 性を直接返す。このUでの右側の結論だけで、一般のiffやopfibration側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.costructuredArrowProjection_rightFibration`

:::

# 4.2.3 Left and Right Covering Maps

%%%
number := false
tag := "kerodon-4-2-3"
%%%

Kerodon [Tag 022K](https://kerodon.net/tag/022K)

:::definition "kerodon_4_2_3_1"
Kerodon Definition 4.2.3.1（[Tag 01QH](https://kerodon.net/tag/01QH)）。対応表の状態：一部。

Prefunctor.IsCovering は star と costar の全単射で、関手の基礎quiverについて仮定すると原文の左・右の一意持ち上げを直接得る。片側だけでよい原文より強い。

宣言：`Prefunctor.IsCovering`、`Prefunctor.star`

:::

:::proposition "kerodon_4_2_3_7"
Kerodon Proposition 4.2.3.7（[Tag 01RS](https://kerodon.net/tag/01RS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。一意な通常圏の辺の持ち上げと離散ファイバーの判定。Quiver の star/costar はファイバー圏の離散性を参照しない。

:::

:::definition "kerodon_4_2_3_8"
Kerodon Definition 4.2.3.8（[Tag 022N](https://kerodon.net/tag/022N)）。対応表の状態：一部。

LeftFibration/RightFibration は原文と同じホーン族について持ち上げの存在部分を直接表す。一意性を要求するcoveringの条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration`

:::

:::proposition "kerodon_4_2_3_16"
Kerodon Proposition 4.2.3.16（[Tag 022W](https://kerodon.net/tag/022W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。nerve を底とする左・右被覆と通常圏の被覆関手の両方向の比較。Quiver の被覆には nerve の比較がない。

:::

:::corollary "kerodon_4_2_3_18"
Kerodon Corollary 4.2.3.18（[Tag 022Y](https://kerodon.net/tag/022Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左被覆を各標準単体への底変換における通常圏の左被覆で判定する iff。ホーンの持ち上げの底変換は一意性を扱わない。

:::

:::proposition "kerodon_4_2_3_19"
Kerodon Proposition 4.2.3.19（[Tag 022Z](https://kerodon.net/tag/022Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左または右の一意ホーン充填と頂点全単射から同型を得る iff。頂点全射な充満忠実射の結論は圏同値。

:::

:::corollary "kerodon_4_2_3_20"
Kerodon Corollary 4.2.3.20（[Tag 0230](https://kerodon.net/tag/0230)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左／右の一意ホーン充填と Kan fibration の組で被覆を判定する iff。LeftFibration と Kan fibration の型は一意性を含まない。

:::

# 4.2.4 Left Anodyne and Right Anodyne Morphisms

%%%
number := false
tag := "kerodon-4-2-4"
%%%

Kerodon [Tag 014S](https://kerodon.net/tag/014S)

:::definition "kerodon_4_2_4_1"
Kerodon Definition 4.2.4.1（[Tag 014T](https://kerodon.net/tag/014T)）。対応表の状態：一部。

leftAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。原文の最小性との同定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn`

:::

:::definition "kerodon_4_2_4_2"
Kerodon Variant 4.2.4.2（[Tag 014U](https://kerodon.net/tag/014U)）。対応表の状態：一部。

rightAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。最小弱飽和閉包との逆包含は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn`

:::

:::proposition "kerodon_4_2_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, CategoryTheory.MorphismProperty.rlp_llp_rlp")
Kerodon Proposition 4.2.4.5（[Tag 014X](https://kerodon.net/tag/014X)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 q、左右それぞれのホーン族に一般等式を適用（Kerodon と一致）。結論：(T.rlp.llp).rlp = T.rlp により、左右それぞれで対応するアノダイン族に対する右持ち上げ性とホーンによる定義が同値（一致）。

:::

:::proposition "kerodon_4_2_4_7"
Kerodon Proposition 4.2.4.7（[Tag 014Z](https://kerodon.net/tag/014Z)）。対応表の状態：一部。

exists\_leftAnodyne\_leftFibration\_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_leftAnodyne_leftFibration_factorization`

:::

:::definition "kerodon_4_2_4_8"
Kerodon Variant 4.2.4.8（[Tag 0150](https://kerodon.net/tag/0150)）。対応表の状態：一部。

exists\_rightAnodyne\_rightFibration\_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization`

:::

:::corollary "kerodon_4_2_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions")
Kerodon Corollary 4.2.4.9（[Tag 0151](https://kerodon.net/tag/0151)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 i（Kerodon と一致）。結論：左右のアノダイン族はいずれも対応するファイブレーション族に対する左持ち上げ性で定義（一致）。

:::

:::proposition "kerodon_4_2_4_10"
Kerodon Proposition 4.2.4.10（[Tag 05HW](https://kerodon.net/tag/05HW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。第0頂点から Λⁿⱼ へ低次元の左ホーンを一枚ずつ付ける有限フィルトレーション。標準単体への包含の補題は終域が Δⁿ。

:::

:::corollary "kerodon_4_2_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stdSimplex_firstVertex_leftAnodyne")
Kerodon Corollary 4.2.4.11（[Tag 05HX](https://kerodon.net/tag/05HX)）。対応表の状態：本体にある。

仮定：任意の自然数 n（Kerodon と一致）。結論：標準 n 単体の第0頂点の Yoneda で表した包含が左アノダイン（一致）。

:::

:::corollary "kerodon_4_2_4_12"
Kerodon Corollary 4.2.4.12（[Tag 0231](https://kerodon.net/tag/0231)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。左アノダインに対する一意な持ち上げと次数ごとの集合の引き戻しとの同値。rlp の既存等式は存在しか扱わない。

:::

# 4.2.5 Exponentiation for Left and Right Fibrations

%%%
number := false
tag := "kerodon-4-2-5"
%%%

Kerodon [Tag 0152](https://kerodon.net/tag/0152)

:::proposition "kerodon_4_2_5_1"
Kerodon Proposition 4.2.5.1（[Tag 00TP](https://kerodon.net/tag/00TP)）。対応表の状態：本体にある。

仮定：単体集合の単射 i と左または右ファイブレーション p、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：内部 Hom の制限比較射 π が p と同じ側のファイブレーション（一致）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_4_2_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.ihom_map_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalIhom_map_rightFibration")
Kerodon Corollary 4.2.5.2（[Tag 00TQ](https://kerodon.net/tag/00TQ)）。対応表の状態：本体にある。

仮定：任意の単体集合 A と左または右ファイブレーション p（Kerodon と一致）。結論：Fun(A,−) の p での作用が p と同じ側のファイブレーション（一致）。

:::

:::proposition "kerodon_4_2_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_right, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightAnodyne_pushoutObjObj_right")
Kerodon Proposition 4.2.5.3（[Tag 0153](https://kerodon.net/tag/0153)）。対応表の状態：本体にある。

仮定：2 本の単射と片方の左または右アノダイン性。アノダイン側の単射は型で別の引数にしない（Lean が弱い：アノダイン性から得る）。結論：積の押し出し比較射 ι が左または右アノダイン。右版は積の因子交換で原文の順序に戻る（一致）。

:::

:::proposition "kerodon_4_2_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalTrivialKanFibration_relativeHom_of_rightAnodyne")
Kerodon Proposition 4.2.5.4（[Tag 0154](https://kerodon.net/tag/0154)）。対応表の状態：本体にある。

仮定：i が左または右アノダインで p が同じ側のファイブレーション、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：Fun(B,X) から制限と後合成を組にした比較射 π が自明 Kan ファイブレーション（一致）。

:::

# 4.2.6 The Homotopy Extension Lifting Property

%%%
number := false
tag := "kerodon-4-2-6"
%%%

Kerodon [Tag 00T8](https://kerodon.net/tag/00T8)

:::proposition "kerodon_4_2_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_5_4_9, kerodon_3_1_2_10, kerodon_4_2_5_4")
Kerodon Proposition 4.2.6.1（[Tag 00TE](https://kerodon.net/tag/00TE)）。対応表の状態：一部。

relativeEdgeSource\_trivialKanFibration は left fibration⇒ev₀の自明Kan性という原文の向きを直接返す。右側のiffと逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource_trivialKanFibration`

:::

:::corollary "kerodon_4_2_6_2" (uses := "kerodon_1_1_0_6, kerodon_4_2_6_1")
Kerodon Corollary 4.2.6.2（[Tag 0155](https://kerodon.net/tag/0155)）。対応表の状態：一部。

kanIntervalEvaluation\_trivialKanFibration は底が一点で X が Kan のときの ev₁ の自明Kan性を直接返す。相対の二端点の同時判定・逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIntervalEvaluation_trivialKanFibration`

:::

