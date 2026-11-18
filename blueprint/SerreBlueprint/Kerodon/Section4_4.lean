import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreRightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathFinalLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeInvolution
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHorn
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationYoneda
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
import SerrePositivity.KST.LocalizingInvariants.CoreInclusionEquivalenceLifting
import SerrePositivity.KST.SConstruction.KanSourceCoreMap

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.4 Isomorphisms and Isofibrations" =>
%%%
number := false
tag := "kerodon-4-4"
%%%

Kerodon の 4.4 節（[Tag 01EM](https://kerodon.net/tag/01EM)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.4.1 Isofibrations of ∞-Categories

%%%
number := false
tag := "kerodon-4-4-1"
%%%

Kerodon [Tag 01ER](https://kerodon.net/tag/01ER)

:::definition "kerodon_4_4_1_1"
Kerodon Definition 4.4.1.1（[Tag 01EN](https://kerodon.net/tag/01EN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏で指定した終点への同型の厳密な持ち上げ。InvertibleTargetLifting の対象は単体集合。

:::

:::proposition "kerodon_4_4_1_3"
Kerodon Proposition 4.4.1.3（[Tag 01EQ](https://kerodon.net/tag/01EQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏の isofibration が F.op と同値。EquivalenceLifting.op の対象は SSet。

:::

:::definition "kerodon_4_4_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting") (uses := "kerodon_1_4_0_1, kerodon_4_1_1_1")
Kerodon Definition 4.4.1.4（[Tag 01ES](https://kerodon.net/tag/01ES)）。対応表の状態：本体にある。

equivalenceLifting\_iff\_inner\_and\_invertibleTargetLifting の右辺は、原文と同じ inner 性と終点指定の可逆辺の可逆な持ち上げ。原文と同じ準圏間の仮定で EquivalenceLifting が二条件と同値になるので、別名でも定義全体を表す。

:::

:::proposition "kerodon_4_4_1_7"
Kerodon Proposition 4.4.1.7（[Tag 01EU](https://kerodon.net/tag/01EU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。F の isofibration と hF における同型の厳密な持ち上げの iff。既存の持ち上げ条件は辺を直接取る。

:::

:::corollary "kerodon_4_4_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.op, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting")
Kerodon Corollary 4.4.1.8（[Tag 01EV](https://kerodon.net/tag/01EV)）。対応表の状態：本体にある。

仮定：∞ 圏間の F（Lean が弱い：EquivalenceLifting.op 自体は任意の単体集合間で成り立つ）。結論：EquivalenceLifting は ∞ 圏上では内ファイブレーションと同値辺持ち上げの組。反転で保たれ、二重反転が恒等なので反対方向にも保たれる（一致）。

:::

:::corollary "kerodon_4_4_1_9"
Kerodon Corollary 4.4.1.9（[Tag 056Z](https://kerodon.net/tag/056Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。正準写像 C→N(hC) の isofibration 性。h の随伴の単位が存在することだけでは同型の持ち上げは得られない。

:::

:::proposition "kerodon_4_4_1_11" (uses := "kerodon_1_4_0_1, kerodon_4_4_2_11, kerodon_5_6_7_5")
Kerodon Example 4.4.1.11（[Tag 01EW](https://kerodon.net/tag/01EW)）。対応表の状態：一部。

leftFibration\_invertibleTargetLifting は原文のleft fibration側の可逆辺を可逆な辺へ持ち上げる条件を直接返す。一般のright側とisofibrationとの同値の一式は引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_invertibleTargetLifting`

:::

# 4.4.2 Isomorphisms and Lifting Properties

%%%
number := false
tag := "kerodon-4-4-2"
%%%

Kerodon [Tag 019C](https://kerodon.net/tag/019C)

:::proposition "kerodon_4_4_2_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_2_6")
Kerodon Proposition 4.4.2.1（[Tag 019D](https://kerodon.net/tag/019D)）。対応表の状態：一部。

kanComplex\_iff\_isGroupoid と kanComplex\_of\_leftHornFillers は原文の (b)⇔(c) の準圏上での比較と (e)⇒(b) を直接与える。right fibrationを含む六条件全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanComplex_of_leftHornFillers`

:::

:::corollary "kerodon_4_4_2_2"
Kerodon Corollary 4.4.2.2（[Tag 02BV](https://kerodon.net/tag/02BV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。Duskin nerve の Kan 性と 2-groupoid 性の iff。通常圏の nerve と IsGroupoid の比較は次元が異なる。

:::

:::corollary "kerodon_4_4_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex")
Kerodon Corollary 4.4.2.3（[Tag 019E](https://kerodon.net/tag/019E)）。対応表の状態：本体にある。

仮定：q:X→S が左または右ファイブレーションで s が S の頂点（Kerodon と一致）。結論：引き戻しで定めた vertexFiber q s が KanComplex（一致）。

:::

:::corollary "kerodon_4_4_2_4"
Kerodon Corollary 4.4.2.4（[Tag 01GY](https://kerodon.net/tag/01GY)）。対応表の状態：一部。

relativeFunctorSpace\_kanComplex は A=∅、qがleft fibrationの場合の同じ底上の写像空間のKan性を直接返す。任意の境界制限とanodyne時の可縮性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex`

:::

:::corollary "kerodon_4_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.relativeFunctorSpace_kanComplex_of_rightFibration")
Kerodon Corollary 4.4.2.5（[Tag 01GZ](https://kerodon.net/tag/01GZ)）。対応表の状態：本体にある。

仮定：q:X→S が左または右ファイブレーションで g:B→S は任意（Kerodon と一致）。結論：底上の相対関手空間 relativeFunctorSpace q g が KanComplex（一致）。

:::

:::theorem "kerodon_4_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_iff_hasFinalHornFillers, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_hasInitialHornFillers")
Kerodon Theorem 4.4.2.6（[Tag 019F](https://kerodon.net/tag/019F)）。対応表の状態：本体にある。

仮定：Quasicategory X と端点を指定した辺 e（Kerodon と一致）。結論：IsInvertibleEdge e と、初辺を固定した最初の外ホーン充填性、終辺を固定した最後の外ホーン充填性はそれぞれ同値（一致）。

:::

:::definition "kerodon_4_4_2_7"
Kerodon Definition 4.4.2.7（[Tag 019G](https://kerodon.net/tag/019G)）。対応表の状態：なし。

isLimitCone\_of\_conservative\_image は原文の保守性を入力仮定に使う別の極限反映の定理。入力仮定の文字列の一致だけは保守性を定義する宣言の対応としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image`

:::

:::proposition "kerodon_4_4_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge")
Kerodon Proposition 4.4.2.11（[Tag 019K](https://kerodon.net/tag/019K)）。対応表の状態：本体にある。

仮定：Quasicategory X,Y と左または右ファイブレーション q:X→Y（Kerodon と一致）。結論：任意の辺 e について q(e) が可逆なら e も可逆（一致）。

:::

:::corollary "kerodon_4_4_2_12" (uses := "kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_4_2_11")
Kerodon Corollary 4.4.2.12（[Tag 02BW](https://kerodon.net/tag/02BW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。F が同型を反映することから左右の slice の後合成も同型を反映する主張。相対制限の fibration 補題は別の条件。

:::

:::proposition "kerodon_4_4_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_initialHorn")
Kerodon Proposition 4.4.2.13（[Tag 01H0](https://kerodon.net/tag/01H0)）。対応表の状態：本体にある。

仮定：∞ 圏間の内ファイブレーション q、次元≥2 の最後のホーン、可換な底単体と可逆な終辺（Kerodon と一致）。結論：ホーン制限と q による像の双方を保つ充填が存在。引用は最初のホーンの双対版も含む（一致）。

:::

:::proposition "kerodon_4_4_2_14" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_4_2_15")
Kerodon Proposition 4.4.2.14（[Tag 01NU](https://kerodon.net/tag/01NU)）。対応表の状態：一部。

rightFibration\_trivialKanFibration\_of\_contractible\_fibers は原文(3)⇒(1)を直接返す。vertexFiber\_isContractibleKanも逆向きの可縮性成分を持つが、left側の全比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan`

:::

:::lemma_ "kerodon_4_4_2_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_3_1_2_12, kerodon_4_2_5_3, kerodon_4_4_2_6")
Kerodon Lemma 4.4.2.15（[Tag 01A7](https://kerodon.net/tag/01A7)）。対応表の状態：なし。

引用はright fibrationと標準単体の最初の頂点の可縮fiber。原文はleft fibrationと最後の頂点を指定しており、opを取る比較をさらに必要とする双対命題そのものはpartialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fillBoundary_over_stdSimplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_liftBoundaryPrism`

:::

# 4.4.3 The Core of an ∞-Category

%%%
number := false
tag := "kerodon-4-4-3"
%%%

Kerodon [Tag 01CZ](https://kerodon.net/tag/01CZ)

:::definition "kerodon_4_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor")
Kerodon Construction 4.4.3.1（[Tag 01D0](https://kerodon.net/tag/01D0)）。対応表の状態：本体にある。

仮定：∞ 圏 X（Lean が弱い：構成は任意の SSet に定義）。結論：各辺が可逆な単体の部分複体 quasicategoryCore X（一致）。

:::

:::proposition "kerodon_4_4_3_6" (lean := "SerrePositivity.KST.LocalizingInvariants.coreInclusion_innerFibration, SerrePositivity.KST.LocalizingInvariants.coreInclusion_equivalenceLifting") (uses := "kerodon_1_4_0_1")
Kerodon Proposition 4.4.3.6（[Tag 01D4](https://kerodon.net/tag/01D4)）。対応表の状態：本体にある。

coreInclusion\_equivalenceLifting と equivalenceLifting\_iff\_inner\_and\_invertibleTargetLifting により、同じcore包含は原文のisofibrationの二条件をともに満たす。coreInclusion\_innerFibrationも直接あり、名称の差だけでpartialにしない。

:::

:::proposition "kerodon_4_4_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_rightFibration_of_invertibleTargetLifting")
Kerodon Proposition 4.4.3.7（[Tag 01EZ](https://kerodon.net/tag/01EZ)）。対応表の状態：本体にある。

仮定：∞ 圏 X,Y と EquivalenceLifting を持つ p:X→Y（Kerodon と一致）。結論：quasicategoryCoreMap p が Kan ファイブレーション（一致）。

:::

:::corollary "kerodon_4_4_3_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_1_11, kerodon_4_4_2_11, kerodon_4_4_3_7")
Kerodon Corollary 4.4.3.8（[Tag 01NV](https://kerodon.net/tag/01NV)）。対応表の状態：一部。

rightFibration\_fibration\_of\_kanComplex は始域もKanと仮定すると原文(3)⇒(1)を同じqについて直接返す。fibration\_leftFibrationは(1)⇒(2)。始域が任意の場合と保守的isofibrationの条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fibration_of_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_leftFibration`

:::

:::corollary "kerodon_4_4_3_9"
Kerodon Corollary 4.4.3.9（[Tag 0237](https://kerodon.net/tag/0237)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。Kan 複体を底にする左／右被覆の同値。Quiver の被覆はホーンを用いない。

:::

:::corollary "kerodon_4_4_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex")
Kerodon Corollary 4.4.3.10（[Tag 01NW](https://kerodon.net/tag/01NW)）。対応表の状態：本体にある。

仮定：KanComplex X,Y と EquivalenceLifting を持つ p:X→Y（Kerodon と一致）。結論：p が Kan ファイブレーション（一致）。

:::

:::corollary "kerodon_4_4_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex")
Kerodon Corollary 4.4.3.11（[Tag 01H1](https://kerodon.net/tag/01H1)）。対応表の状態：本体にある。

仮定：Quasicategory X（Kerodon と一致）。結論：quasicategoryCore X を単体集合として見たものが KanComplex（一致）。

:::

:::corollary "kerodon_4_4_3_13"
Kerodon Corollary 4.4.3.13（[Tag 04Q5](https://kerodon.net/tag/04Q5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。replete 部分圏の core が元の core の直和因子になる主張。全部分複体の包含に直和分解を与える型がない。

:::

:::corollary "kerodon_4_4_3_14"
Kerodon Corollary 4.4.3.14（[Tag 01D6](https://kerodon.net/tag/01D6)）。対応表の状態：一部。

kanSource\_edge\_isInvertible と IsInvertibleEdge.map により、Kan複体の辺をFで送ったuは可逆で、原文(2)⇒(1)を直接得る。逆にKan/可縮Kanからの表示を構成する方向は含まない。

宣言：`SerrePositivity.KST.SConstruction.kanSource_edge_isInvertible`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers`

:::

:::corollary "kerodon_4_4_3_15" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Corollary 4.4.3.15（[Tag 01H3](https://kerodon.net/tag/01H3)）。対応表の状態：一部。

exists\_equivalenceInterval\_map\_of\_vertexIso は、二対象の同型から同じ二頂点を持つ可逆区間からの射を直接与える。可逆区間はcodiscreteな二点亜群のnerveで可縮Kanであり、(1)から存在条件への向き。一般の逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_equivalenceInterval_map_of_vertexIso`

:::

:::definition "kerodon_4_4_3_16"
Kerodon Notation 4.4.3.16（[Tag 01D7](https://kerodon.net/tag/01D7)）。対応表の状態：一部。

nonempty\_vertexIso\_of\_piZero\_eq をKan coreに適用し包含で送ると、同じπ₀成分の二対象が元のCで同型になる方向を直接得る。同型類の集合との全単射・逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq`

:::

:::proposition "kerodon_4_4_3_17" (lean := "SerrePositivity.KST.SConstruction.kanSourceCoreMap, SerrePositivity.KST.SConstruction.kanSourceCoreMap_inclusion, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift")
Kerodon Proposition 4.4.3.17（[Tag 01D8](https://kerodon.net/tag/01D8)）。対応表の状態：本体にある。

仮定：Kan 始域 X、∞ 圏 Y（Lean が弱い：Y は任意）。結論：任意の f:X→Y を core へ因子化し、包含との合成は f。包含が単射なので逆対応は一意（一致）。

:::

:::corollary "kerodon_4_4_3_18" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_11, kerodon_4_4_3_17")
Kerodon Corollary 4.4.3.18（[Tag 01D9](https://kerodon.net/tag/01D9)）。対応表の状態：一部。

kanSourceCoreMap と包含との厳密な回収式をKan部分複体Aの包含に適用するとA⊆coreを直接得る。原文の最大性の成分。core自身のKan性はこの引用の結論に含まない。

宣言：`SerrePositivity.KST.SConstruction.kanSourceCoreMap`、`SerrePositivity.KST.SConstruction.kanCoreIso`

:::

:::corollary "kerodon_4_4_3_19" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_1_4, kerodon_4_4_3_7, kerodon_4_4_3_11, kerodon_4_4_3_18")
Kerodon Corollary 4.4.3.19（[Tag 01H4](https://kerodon.net/tag/01H4)）。対応表の状態：一部。

quasicategoryCoreMap\_isPullback\_of\_isPullback は同じ指定したcore四角形の厳密なpullback性を直接返す。ホモトピーpullback性・同型の反映・q′のisofibration性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_isPullback_of_isPullback`、`SSet.quasicategory_of_innerFibration`

:::

:::corollary "kerodon_4_4_3_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_isPullback_of_isPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackIso")
Kerodon Corollary 4.4.3.20（[Tag 01H6](https://kerodon.net/tag/01H6)）。対応表の状態：本体にある。

仮定：∞ 圏の isofibration p と底の点（Lean が弱い：p は内ファイブレーション、底変換は任意の ∞ 圏からでよい）。結論：core と当該厳密な引き戻しを交換する同型。点を代入するとファイバーの比較になる（一致）。

:::

:::corollary "kerodon_4_4_3_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceOverPostcomp_equivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceUnderPostcomp_equivalenceLifting")
Kerodon Corollary 4.4.3.21（[Tag 069C](https://kerodon.net/tag/069C)）。対応表の状態：本体にある。

仮定：EquivalenceLifting を持つ p と任意の図式 f:K→X（Kerodon と一致）。結論：sliceOverPostcomp f p も EquivalenceLifting。coslice の双対も含む（一致）。

:::

:::corollary "kerodon_4_4_3_22"
Kerodon Corollary 4.4.3.22（[Tag 04HW](https://kerodon.net/tag/04HW)）。対応表の状態：一部。

qにさらにrightまたはleft fibrationを仮定すると、vertexFiber\_kanComplexの二宣言から同じ指定fiberのKan性を直接得る。保守的isofibrationだけからの導出は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration`

:::

:::proposition "kerodon_4_4_3_23" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_17")
Kerodon Proposition 4.4.3.23（[Tag 01DA](https://kerodon.net/tag/01DA)）。対応表の状態：なし。

equivalencePathι\_isIso\_of\_kanComplex の始域は可逆辺の部分複体で、原文はKanパラメータからの関手空間のcore比較。Δ¹はKanでもなく、原文の特殊形としてこの型をそのまま使えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι_isIso_of_kanComplex`

:::

# 4.4.4 Natural Isomorphisms

%%%
number := false
tag := "kerodon-4-4-4"
%%%

Kerodon [Tag 01DF](https://kerodon.net/tag/01DF)

:::definition "kerodon_4_4_4_1"
Kerodon Definition 4.4.4.1（[Tag 01DG](https://kerodon.net/tag/01DG)）。対応表の状態：なし。

FunctorIsoは関手空間のホモトピー圏の同型データ。原文の実際の可逆な自然変換の辺を与える型ではなく、代表を選んで比較する宣言がさらに必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex`

:::

:::theorem "kerodon_4_4_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy")
Kerodon Theorem 4.4.4.4（[Tag 01DK](https://kerodon.net/tag/01DK)）。対応表の状態：本体にある。

仮定：Quasicategory X、図式 f,g:K→X と関手空間の辺 e（Kerodon と一致）。結論：辺の可逆性と、任意の K の頂点で評価した辺の可逆性が同値（一致）。

:::

:::corollary "kerodon_4_4_4_6"
Kerodon Corollary 4.4.4.6（[Tag 01DM](https://kerodon.net/tag/01DM)）。対応表の状態：なし。

quasicategoryCoreProduct は比較射の構成だけで同型性・普遍性を述べない。指定関手の極限保存の特殊形を直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreProduct`

:::

:::lemma_ "kerodon_4_4_4_7" (uses := "kerodon_1_1_0_6, kerodon_3_1_2_11")
Kerodon Lemma 4.4.4.7（[Tag 01DN](https://kerodon.net/tag/01DN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。Δᵐ×Δⁿ の指定始辺を保つ外ホーン付き有限フィルトレーション。prism の既存分解は Δ¹ または別の境界を使う。

:::

:::lemma_ "kerodon_4_4_4_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_2_13, kerodon_4_4_4_7")
Kerodon Lemma 4.4.4.8（[Tag 01DP](https://kerodon.net/tag/01DP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。全頂点を含む A 上の相対ホーン図式を与え、各点のファイバーの辺が可逆なときの延長。一般の inner fibration での当該比較は未発見。

:::

:::proposition "kerodon_4_4_4_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_2_6, kerodon_4_4_4_8")
Kerodon Proposition 4.4.4.9（[Tag 023A](https://kerodon.net/tag/023A)）。対応表の状態：なし。

isInvertibleEdge\_vertexFiber\_iff はfiberの辺と全空間の辺の可逆性の比較。原文は底上の関手空間での可逆性と各評価fiberでの可逆性の比較で、Bが一点でも対象同定がさらに必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_vertexFiber_iff`

:::

# 4.4.5 Exponentiation for Isofibrations

%%%
number := false
tag := "kerodon-4-4-5"
%%%

Kerodon [Tag 01F0](https://kerodon.net/tag/01F0)

:::proposition "kerodon_4_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom")
Kerodon Proposition 4.4.5.1（[Tag 01F1](https://kerodon.net/tag/01F1)）。対応表の状態：本体にある。

仮定：EquivalenceLifting を持つ U、単射 i、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：Fun(B,C) から制限と U による後合成を組にした比較射が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre")
Kerodon Corollary 4.4.5.3（[Tag 01F3](https://kerodon.net/tag/01F3)）。対応表の状態：本体にある。

仮定：Quasicategory X と単射 i:A→B（Kerodon と一致）。結論：制限 (pre i).app X が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_3_7, kerodon_4_4_5_3")
Kerodon Corollary 4.4.5.4（[Tag 01F4](https://kerodon.net/tag/01F4)）。対応表の状態：本体にある。

equivalenceLifting\_pre が同じ制限射にEquivalenceLiftingを返し、それをcoreMap\_fibration\_of\_kanEquivalenceLiftingにそのまま代入すると原文のcore制限射のKan fibration性を得る。仮定・対象・射が一致し追加の数学的比較は要らない。

:::

:::corollary "kerodon_4_4_5_5" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_3")
Kerodon Corollary 4.4.5.5（[Tag 02QY](https://kerodon.net/tag/02QY)）。対応表の状態：なし。

二つの端点への各射影の自明Kan性は、両端の組への原文の射のisofibration性ではない。別の射の性質だけをcomponentにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_zero`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_one`

:::

:::corollary "kerodon_4_4_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom")
Kerodon Corollary 4.4.5.6（[Tag 01H7](https://kerodon.net/tag/01H7)）。対応表の状態：本体にある。

仮定：EquivalenceLifting を持つ U と任意の単体集合 K（Kerodon と一致）。結論：(ihom K).map U が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePathReplacementMap_internalHom_fibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_7, kerodon_4_4_5_6")
Kerodon Corollary 4.4.5.7（[Tag 02QZ](https://kerodon.net/tag/02QZ)）。対応表の状態：本体にある。

EquivalenceLifting.internalHom に任意Bを代入し、coreMap\_fibration\_of\_kanEquivalenceLiftingをその結果に適用すると、原文の同じ内部Homのcore後合成のKan fibration性を得る。isofibrationとの比較は二条件のiffで確認済み。

:::

:::proposition "kerodon_4_4_5_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_1_2_12, kerodon_4_4_2_13, kerodon_4_4_4_8")
Kerodon Proposition 4.4.5.8（[Tag 01NX](https://kerodon.net/tag/01NX)）。対応表の状態：一部。

prism\_lift\_boundary\_with\_final\_endpoint は B=Δ\^(n+1)、A=その境界で最後の垂直辺が可逆な原文と同じprism持ち上げを直接返す。Aが全頂点を含む次元とその境界形に限る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prism_lift_boundary_with_final_endpoint`

:::

:::corollary "kerodon_4_4_5_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_4_4_5_8")
Kerodon Corollary 4.4.5.9（[Tag 01NY](https://kerodon.net/tag/01NY)）。対応表の状態：なし。

relativeEquivalencePathMapAtの自明Kan性は特定の可逆path空間の持ち上げ。原文の点ごとに可逆なprism全体をその空間に入れる比較と条件の同定を型で与えず、証明部品にとどまる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration`

:::

:::corollary "kerodon_4_4_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_zero, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_one, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath")
Kerodon Corollary 4.4.5.10（[Tag 02BY](https://kerodon.net/tag/02BY)）。対応表の状態：本体にある。

仮定：Quasicategory X（Kerodon と一致）。結論：可逆辺が張る Fun(Δ¹,X) の全部分複体 equivalencePath X からの 0,1 での評価がともに自明 Kan ファイブレーション（一致）。

:::

:::definition "kerodon_4_4_5_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Variant 4.4.5.11（[Tag 01NZ](https://kerodon.net/tag/01NZ)）。対応表の状態：一部。

FにさらにEquivalenceLifting（isofibration）を仮定すると relativeInternalHom が同じ比較射F′のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom`

:::

:::corollary "kerodon_4_4_5_12"
Kerodon Corollary 4.4.5.12（[Tag 069D](https://kerodon.net/tag/069D)）。対応表の状態：一部。

kanEquivalenceLifting\_relativeFunctorOverPre\_of\_cocartesian はFがcocartesian fibrationである場合、同じ底上の関手空間の制限射のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian`

:::

