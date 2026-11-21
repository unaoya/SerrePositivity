-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import SerrePositivity.InfinityCategories.HTT.Section2_4_1.CartesianComparisonBoundary
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComma
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.AllEdges
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianCancellation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPrismExtension
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightFibrationFiberCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparisonFibers
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InitialObjectsInSlices
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCosliceCancellation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingTrivial
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceRetraction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightConeBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 2.4 Cartesian Fibrations" =>
%%%
number := false
tag := "htt-2-4"
%%%

HTT 2.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.4.1 Cartesian Morphisms

%%%
number := false
tag := "htt-2-4-1"
%%%

:::definition "htt_2_4_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge")
*HTT 定義 2.4.1.1*　相対スライスによる Cartesian 辺（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=133)）。対応表の状態：本体にある。

*主張*　内ファイブレーション $`p:X\to S` の辺 $`f:x\to y` が $`p`-Cartesian であるとは、$`X_{/f}\to X_{/y}\times_{S_{/p(y)}} S_{/p(f)}` が自明 Kan ファイブレーションであることをいう。

仮定：内ファイブレーション p とその始域の辺（Lean が弱い：定義自体は p の内ファイブレーション性を要求しない）。結論：最後の辺を固定した外ホーンの相対持ち上げを要求する。HTT の Remark 2.4.1.4 が相対スライスの自明性とこの条件を同定する（一致）。

$`y` へ向かう錐と、底で $`p(f)` に沿った因子分解を指定する。その因子分解が全空間で $`f` を経由して実現されるという普遍性を、相対スライスの比較で表す。

:::

:::proposition "htt_2_4_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsCartesianEdge_of_comp") (uses := "htt_2_0_0_3, htt_2_1_2_1, htt_2_1_3_4")
*HTT 命題 2.4.1.3*　Cartesian 辺の底変換と合成射での消去（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=133)）。対応表の状態：一部（component）。

*主張*　同型のすべての辺は Cartesian であり、Cartesian 辺は底変換で保たれ、内ファイブレーションの合成 $`qp` では $`p(f)` が $`q`-Cartesian なら $`f` の $`p`-Cartesian 性と $`qp`-Cartesian 性は同値である。

KB-W2原文・型再照合：仮定：任意の Cartesian edge の pullback（HTT の (2) と一致）。結論：isCartesianEdge\_pullback はその同じ辺の Cartesian 性を保つので (2) に一致。また comp と、全対象が準圏という追加仮定下の cancellation は (3) の両方向を与える。(1) の全 iso と一般の simplicial sets での cancellation は含まない。

いずれもスライスの相対比較で判定する。底変換後も初めに指定した辺の像が同じなので持ち上げは保たれ、合成では底側の比較がすでに自明であることを使う。

:::

:::proposition "htt_2_4_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge")
*HTT 注意 2.4.1.4*　最後の辺を固定した外ホーンの充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=134)）。対応表の状態：本体にある。

*主張*　$`p`-Cartesian 性は、最後の辺を固定したすべての右外角の相対充填で判定でき、底が一点なら同値辺であることと一致する。

仮定：単体集合の射と指定した辺（Lean が弱い：内ファイブレーション性を仮定しない）。結論：n ≥ 2 の最後の外ホーンで最後の辺が指定辺なら、底上で全単体へ持ち上がることを Cartesian 性とする（一致）。

右外角の最後の二頂点が指定辺をなす。これを固定して底で指定された単体を持ち上げることが、スライスの比較に対する境界持ち上げに当たる。

:::

:::proposition "htt_2_4_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge")
*HTT 命題 2.4.1.5*　可逆辺の Cartesian 性による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=134)）。対応表の状態：本体にある。

*主張*　∞ 圏間の内ファイブレーションの辺が同値であることは、その辺が Cartesian であり、底への像が同値であることと同値である。

仮定：準圏間の内ファイブレーションと指定辺（HTT と一致）。結論：辺が可逆であることと、それが Cartesian で底の像が可逆であることが同値（一致）。

Cartesian 性は底の辺に沿う最適な持ち上げを表すが、底の辺は一般に可逆とは限らない。同値を判定するには、底の可逆性も合わせて調べる。

:::

:::corollary "htt_2_4_1_6" (lean := "SerrePositivity.InfinityCategories.HTT.Section2_4_1.isCartesianEdge_constant")
*HTT 系 2.4.1.6*　恒等辺の Cartesian 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=135)）。対応表の状態：本体にある。

*主張*　∞ 圏間の内ファイブレーションについて、各対象の退化辺は Cartesian である。

仮定：準圏間の内ファイブレーションと頂点（HTT と一致）。結論：頂点における定値辺は Cartesian（一致）。

恒等射は全空間でも底でも可逆である。同値辺を Cartesian と比較する判定をこの退化辺に適用する。

:::

:::proposition "htt_2_4_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long")
*HTT 命題 2.4.1.7*　三角形での Cartesian 辺の合成と消去（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=135)）。対応表の状態：本体にある。

*主張*　二単体 $`x\xrightarrow{f}y\xrightarrow{g}z` の長辺を $`h` とすると、$`g` が Cartesian なら $`f` が Cartesian であることと $`h` が Cartesian であることは同値である。

仮定：底が準圏、内ファイブレーション、三角形の後半の辺が Cartesian（Lean が弱い：始域の準圏性は別に仮定しない）。結論：最初の辺が Cartesian であることと長辺が Cartesian であることが同値（一致）。

普遍性をもつ後半の辺 $`g` で因子分解を比較できるので、その前にある $`f` の普遍性は長辺の普遍性と同じになる。合成の等式の代わりに二単体が指定されている。

:::

:::proposition "htt_2_4_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prism_exists_lift_of_cocartesian_firstEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_hasCocartesianHornLifting") (uses := "htt_2_0_0_3, htt_2_1_2_6, htt_2_4_1_6")
*HTT 命題 2.4.1.8*　余 Cartesian 辺のプリズム充填判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=136)）。対応表の状態：一部（direction）。

*主張*　内ファイブレーションの辺が余 Cartesian であることは、$`\Delta^n\times\Delta^1` の初期面と境界柱、頂点 $`0` 上の指定辺を固定した相対延長が全 $`n\ge1` で可能であることと同値である。

KB-W2原文・型再照合：仮定：inner fibration p と p-cocartesian な指定最初の辺（順方向と一致）。結論：HornLifting との同値を介して prism\_exists\_lift\_of\_cocartesian\_firstEdge を適用すると、原典の各 n≥1 の指定 prism extension を得る。逆向きはない。

上の面をすべて先に指定するのではなく、始点側 $`\Delta^n\times\{0\}` と境界上の変形を固定する。余 Cartesian な辺を開始点に置くことで、残る変形の延長を検査する。

:::

:::proposition "htt_2_4_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCartesianComparisonTriangle, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianComparison_first_isInvertible")
*HTT 注意 2.4.1.9*　同じ終点と底の Cartesian 持ち上げの比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=137)）。対応表の状態：一部（component）。

*主張*　底の辺と全空間の終点を固定した Cartesian な持ち上げは、その辺を持ち上げるスライスの終対象になり、同値まで決まる。

KB-W2原文・型再照合：仮定：同じ底の辺・終点を持つ二つの Cartesian lifts と準圏の底（Lean が強い）。結論：同じ退化底三角形の比較を作り、その残る辺が invertible であると示すので「二つの lifts は equivalent」という明記された assertion に一致。全ての lifts の相対 slice での terminality は含まない。

比較の圏は $`X_{/x}` を底のスライスに写し、指定した底の辺の上で取る。その中の終対象性により、持ち上げの始点も含めて比較できる。

:::

:::definition "htt_2_4_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback")
*HTT 定義 2.4.1.11*　底の辺に制限した局所 Cartesian 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=138)）。対応表の状態：一部（stronger-hyp）。

*主張*　内ファイブレーションの辺を局所 Cartesian というのは、その像 $`\Delta^1\to S` に沿う引き戻し上で Cartesian になる場合である。

KB-W2原文・型再照合：仮定：p-inner fibration の辺 e に大域的 IsCartesianEdge p e を追加（Lean が強い）。結論：isCartesianEdge\_pullback を p(e):Δ1→S への引戻しと diagonal lift e に適用すると、同じ引戻し X×SΔ1 の同じ辺が Cartesian。局所 Cartesian の表示条件はこの追加仮定の下で得るが、元の大域性なしの局所述語を束ねた定義はない。

元の底全体の他の辺と比較する必要を一旦外し、指定辺の張る一単体だけを底として検査する。同じ辺という語は、引き戻し上の対応する辺を指す。

:::

# 2.4.2 Cartesian Fibrations

%%%
number := false
tag := "htt-2-4-2"
%%%

:::definition "htt_2_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_iff_isCocartesianEdge_op")
*HTT 定義 2.4.2.1*　左右の Cartesian ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=139)）。対応表の状態：本体にある。

*主張*　Cartesian ファイブレーションは底の任意の辺を指定終点へ Cartesian に持ち上げられる内ファイブレーションであり、余 Cartesian ファイブレーションはその双対である。

仮定：任意の単体集合の射（HTT と一致）。結論：内ファイブレーションで、終点を指定した Cartesian 持ち上げ、または始点を指定した反対側の持ち上げが存在する（一致）。

指定した終点から逆向きにファイバー間の移送が得られる。反対化した場合は始点を指定して前向きに移送する。

:::

:::proposition "htt_2_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration")
*HTT 注意 2.4.2.2*　Grothendieck ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=139)）。対応表の状態：一部（component）。

*主張*　通常関手の nerve が Cartesian ファイブレーションになることは、その関手が Grothendieck ファイブレーションであることと同値である。

KB-W2原文・型再照合：仮定：通常 F:C→C′、底 C′ は thin（Lean が強い特殊形）。結論：N(C) は準圏なので thinNerve\_innerFibration により N(F) は InnerFibration。明記された自動的 inner 性のこの場合に一致するが、IsFibered F と CartesianFibration N(F) の iff はない。

通常圏の nerve では内ファイブレーションの条件が自動的である。残る条件は、通常圏での Cartesian な射を指定終点へ持ち上げる条件に戻る。

:::

:::proposition "htt_2_4_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_comp, CategoryTheory.MorphismProperty.rlp_of_isIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges")
*HTT 命題 2.4.2.3*　Cartesian ファイブレーションの安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=139)）。対応表の状態：本体にある。

*主張*　Cartesian ファイブレーションの類は同型を含み、底変換と合成に閉じている。

仮定：単体集合の同型、Cartesian ファイブレーションの底変換、または二つの Cartesian ファイブレーションの合成（HTT と一致）。結論：同型は右持ち上げ性から右ファイブレーションとなるので Cartesian。底変換と合成も Cartesian（一致）。

底変換では元の空間で得た持ち上げを新しい底の辺と組み合わせる。合成では底の辺を中間の空間へ、その持ち上げをさらに上の空間へ持ち上げる。

:::

:::proposition "htt_2_4_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex") (uses := "htt_2_0_0_3, htt_2_4_1_4, htt_2_4_2_1")
*HTT 命題 2.4.2.4*　全辺の Cartesian 性と右持ち上げ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=140)）。対応表の状態：一部（component）。

*主張*　内ファイブレーションについて、右ファイブレーションであることは、Cartesian ファイブレーションで全辺が Cartesian であること、または Cartesian ファイブレーションで全ファイバーが Kan であることと同値である。

KB-W2原文・型再照合：仮定：任意の単体集合の射 p（原典より弱い）。結論：rightFibration\_iff\_cartesianFibration\_all\_edges は (1)⇔(2) を正確に与え、vertexFiber\_kanComplex と合わせて (2)⇒(3) も得る。(3)⇒(1)/(2) は含まない。

Cartesian ファイブレーションでは一般に各終点で特別な持ち上げを選ぶ。ファイバーが Kan ならファイバー内の変更は可逆であるため、同じ底の辺上の他の辺にも Cartesian 性が広がる。

:::

:::corollary "htt_2_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_of_cartesianFibration_of_all_edges")
*HTT 系 2.4.2.5*　Cartesian 辺の部分複体と右持ち上げ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=140)）。対応表の状態：一部（stronger-hyp）。

*主張*　Cartesian ファイブレーションの各単体のうち、すべての辺が Cartesian であるものの部分集合を取ると、底への制限が右ファイブレーションになる。

KB-W2原文・型再照合：仮定：CartesianFibration p で全ての辺が p-Cartesian と追加（Lean が強い）。結論：原典の指定 X′ はこの仮定で X 全体なので、rightFibration\_of\_cartesianFibration\_of\_all\_edges は同じ制限射 p\|X′ が right fibration となる。この場合に一致するが一般の Cartesian-edge subcomplex の構成はない。

元の頂点を保ちながら、許す辺とそれらをもつ高次単体を選別する。ファイバー内で許される辺は同値になるので、ファイバーの core を取る構成に当たる。

:::

:::definition "htt_2_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd")
*HTT 定義 2.4.2.6*　局所 Cartesian ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=141)）。対応表の状態：一部（stronger-hyp）。

*主張*　局所 Cartesian ファイブレーションとは、底の各辺 $`\Delta^1\to S` に沿う引き戻しが Cartesian ファイブレーションになる内ファイブレーションをいう。

KB-W2原文・型再照合：仮定：p が大域的 CartesianFibration と追加（Lean が強い）。結論：cartesianFibration\_pullback\_snd を任意の辺 Δ1→S に適用し、その同じ pullback の Cartesian 性を得るので原典の local-Cartesian の条件はこの場合に成り立つ。一般の local lifting と二条件の iff を束ねる型はない。

底の辺と終点の組ごとに局所 Cartesian な持ち上げがある条件ともいえる。この段階では、異なる底の辺の上にある持ち上げの合成について条件を課していない。

:::

:::corollary "htt_2_4_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd")
*HTT 系 2.4.2.10*　二次元以下の底変換による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=143)）。対応表の状態：一部（direction）。

*主張*　内ファイブレーションの Cartesian 性は、底の次元 $`n\le2` のすべての単体に沿う引き戻しで検査できる。

KB-W2原文・型再照合：仮定：p が CartesianFibration（原典 iff の順方向と一致）。結論：任意 Δn→S の pullback は Cartesian なので、とくに n≤2 の条件に一致。逆方向はない。

一次元の引き戻しだけでは個々の局所的な持ち上げを得る。二次元も調べると、底の二辺とその合成に沿う持ち上げの相互作用を検査できる。

:::

:::proposition "htt_2_4_2_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long")
*HTT 注意 2.4.2.14*　局所比較と三角形の Cartesian 消去（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=144)）。対応表の状態：一部（stronger-hyp）。

*主張*　内ファイブレーションの二単体で後半の辺が Cartesian なら、前半または長辺の局所 Cartesian 性を、対応する底辺上の Cartesian 持ち上げの存在を仮定して、もう一方の辺の Cartesian 性へ移せる。

KB-W2原文・型再照合：仮定：底が準圏で p は CartesianFibration、後半の g は Cartesian（原典最後の文に対して Lean が強い）。結論：triangle\_longEdge と triangle\_first\_of\_second\_long で f が Cartesian iff h が Cartesian を得るので「In particular」の assertion に一致。一般の local f/h と別の global lift を使う (a)(b) は含まない。

長辺が局所 Cartesian な場合は前半と同じ底辺の Cartesian 持ち上げを使う。逆の場合は長辺と同じ底辺の持ち上げを使う。写像が Cartesian ファイブレーションならこの存在は自動的である。

:::

# 2.4.3 Stability Properties of Cartesian Fibrations

%%%
number := false
tag := "htt-2-4-3"
%%%

:::proposition "htt_2_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration")
*HTT 命題 2.4.3.1*　スライス射影の Cartesian 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=145)）。対応表の状態：一部（special）。

*主張*　Cartesian ファイブレーション $`p:\mathcal C\to\mathcal D` は、図式 $`q` へのスライス間の Cartesian ファイブレーション $`\mathcal C_{/q}\to\mathcal D_{/pq}` を誘導し、Cartesian 辺は $`\mathcal C` で判定できる。

KB-W2原文・型再照合：仮定：Cartesian ファイブレーション p と図式（Lean が強い：p が右ファイブレーションで、図式を一点に限る）。結論：スライス間の後合成が自明 Kan ファイブレーション（Lean が弱い：一般の図式と、スライスの辺の Cartesian 性を像で判定する同値はない）。

スライスの辺には固定図式 $`q` への錐との整合性が付く。辺が持ち上げとして普遍的かどうかは、その錐を忘れた像によって決まる。

:::

:::proposition "htt_2_4_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceOverPostcomp")
*HTT 命題 2.4.3.2*　スライス射影の余 Cartesian 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=146)）。対応表の状態：一部（special）。

*主張*　余 Cartesian ファイブレーション $`p:\mathcal C\to\mathcal D` からも上のスライス間に余 Cartesian ファイブレーションが誘導され、その余 Cartesian 辺は $`\mathcal C` で判定できる。

KB-W2原文・型再照合：仮定：余 Cartesian ファイブレーションと任意の図式（Lean が強い：元の射が自明 Kan ファイブレーション）。結論：スライス間の後合成も自明 Kan ファイブレーションで、特に余 Cartesian ファイブレーション（Lean が弱い：一般の場合と、元の辺への余 Cartesian 性の反映を含まない）。

余 Cartesian 側でも原典で固定する図式への錐は同じ向きである。結論は余 Cartesian 辺の持ち上げが、その錐を保つ比較にも使えるというもの。

:::

# 2.4.4 Mapping Spaces and Cartesian Fibrations

%%%
number := false
tag := "htt-2-4-4"
%%%

:::lemma_ "htt_2_4_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn")
*HTT 補題 2.4.4.1*　内ファイブレーションによる右写像空間の Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=148)）。対応表の状態：本体にある。

*主張*　∞ 圏間の内ファイブレーション $`p` が誘導する右写像単体集合の比較 $`\operatorname{Hom}^R(X,Y)\to\operatorname{Hom}^R(pX,pY)` は Kan ファイブレーションである。

仮定：準圏間の内ファイブレーションと二頂点（HTT と一致）。結論：右写像空間の誘導射が全ホーンを右に持ち上げるため Kan ファイブレーション（一致）。

両端は全空間と底で対応して固定する。その下で底の写像単体集合の角を持ち上げることを、元の内ファイブレーションの持ち上げへ還元する。

:::

:::corollary "htt_2_4_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isQCatEquivalence_of_rightFibration_fibers") (uses := "htt_1_1_2_4, htt_2_4_1_1, htt_2_4_2_1")
*HTT 系 2.4.4.4*　局所 Cartesian 射の繊維同値判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=150)）。対応表の状態：一部（special）。

*主張*　同じ底上の局所 Cartesian ファイブレーション間で、局所 Cartesian 辺を保ち、各頂点ファイバーで圏同値を誘導する関手は全空間でも圏同値である。

KB-W2原文・型再照合：仮定：底上の射と各繊維の準圏同値（Lean が強い：二つの射影は右ファイブレーションで底は準圏）。結論：全空間の比較射は準圏同値（一致する特別な場合）。

ファイバー内の比較だけでは異なるファイバー間の射を扱えない。局所 Cartesian な持ち上げを保つ条件を加えることで、それらの射の同値を底の辺ごとに調べられる。

:::

:::corollary "htt_2_4_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.isQCatEquivalence") (uses := "htt_1_1_2_4, htt_2_4_2_1")
*HTT 系 2.4.4.5*　圏同値に沿う Cartesian 射の底変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=150)）。対応表の状態：一部（stronger-hyp）。

*主張*　∞ 圏間の Cartesian ファイブレーションを底の圏同値で引き戻すと、新しい全空間から元の全空間への射は圏同値である。

KB-W2原文・型再照合：仮定：C,D,D′ は準圏、Cartesian p にさらに EquivalenceLifting p を明示して追加（Lean が強い）。結論：同じ pullback projection q′ は IsPrecompositionEquivalence、pullback の準圏性の下で IsQCatEquivalence に一致する。Cartesian 性から追加 lifting を導く比較は含めず、追加仮定の下だけを数える。

引き戻し後のファイバーは元の対応するファイバーと同じである。底も同値なので、底とファイバーを組み合わせて全空間を比較できる。

:::

:::corollary "htt_2_4_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.trivialKanFibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration") (uses := "htt_1_1_2_4, htt_2_1_3_4, htt_2_4_2_1, htt_2_4_2_4")
*HTT 系 2.4.4.6*　Cartesian ファイブレーションの自明性判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=150)）。対応表の状態：一部（stronger-hyp）。

*主張*　∞ 圏間の Cartesian ファイブレーションが圏同値であることは、それが自明ファイブレーションであることと同値である。

KB-W2原文・型再照合：仮定：準圏間の Cartesian p にさらに EquivalenceLifting p を追加（Lean が強い）。結論：native QCatEquivalence⇒TrivialKanFibration と逆方向の二宣言で、同じ p の iff を得る。Cartesian 性から EquivalenceLifting を導く型はここでは得ていない。

Cartesian ファイブレーションには圏論的ファイブレーションの条件がある。そのクラスでは圏同値を加えると、単体的集合の境界に対する持ち上げが得られる。

:::

:::lemma_ "htt_2_4_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isInitialVertex_of_initialBoundaryLifting_of_image")
*HTT 補題 2.4.4.7*　底と繊維の始対象から全体の始対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=151)）。対応表の状態：本体にある。

*主張*　Cartesian ファイブレーションの底で始対象である点の上にあるファイバーの始対象は、全空間の始対象である。

仮定：準圏の Cartesian ファイブレーション、ある繊維の始対象とその像が底の始対象（HTT と一致）。結論：繊維内の始対象性から相対境界を充填でき、像の始対象性と合わせて全空間でも始対象（一致）。

まず底で指定対象へ向かう射を選び、それを Cartesian に持ち上げて写像の問題を始点側ファイバーへ戻す。そこでの始対象性が全空間での比較を与える。

:::

:::lemma_ "htt_2_4_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting")
*HTT 補題 2.4.4.8*　繊維の始対象を固定した相対境界充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=151)）。対応表の状態：本体にある。

*主張*　Cartesian ファイブレーションに対する $`n>0` の境界持ち上げ問題で、指定境界の最初の頂点が対応ファイバーの始対象なら、相対的に単体へ延長できる。

仮定：Cartesian ファイブレーションと正次元境界の第 0 頂点が繊維の始対象（HTT と一致。Lean の準圏性は底を指定標準単体へ引き戻せば得られる）。結論：指定された底の単体を保って、境界を全単体へ延長できる（一致）。

任意の始点について主張するのではなく、最初の頂点をファイバー内の始対象として指定する。そこからの射の普遍性が、境界の他の面を固定した延長に使われる。

:::

# 2.4.5 Application: Invariance of Undercategories

%%%
number := false
tag := "htt-2-4-5"
%%%

:::lemma_ "htt_2_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver_fiber_equivalence_iff") (uses := "htt_1_1_2_1, htt_1_1_2_4, htt_2_1_2_1, htt_2_1_2_5, htt_2_1_3_3")
*HTT 補題 2.4.5.1*　充満忠実写像によるコスライス繊維の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=152)）。対応表の状態：一部（special）。

*主張*　充満忠実な $`p:\mathcal C\to\mathcal D` と図式 $`j` および対象 $`x` に対し、頂点を $`x` に固定した余錐の Kan 複体から $`pj` の頂点 $`p(x)` のものへの比較はホモトピー同値である。

KB-W2原文・型再照合：仮定：fully faithful な準圏間の G、K を一点の図式 x に限定（Lean が強い特殊形）。結論：cosliceComparisonOver\_fiber\_equivalence\_iff の右辺は fully faithfulness の同じ pinchedHomMap の同値であるため、指定 coslice-fiber comparison は同値。両 fiber は Kan なので原典のこの homotopy-equivalence assertion に一致する。一般の K は含まない。

余錐のひとつの脚だけではなく、頂点を固定して図式全体からそこへ向かう整合的データを比較する。充満忠実性はこれらの脚の写像型を変えない。

:::

# 2.4.6 Application: Categorical Fibrations over a Point

%%%
number := false
tag := "htt-2-4-6"
%%%

:::lemma_ "htt_2_4_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.exists_strict_retraction")
*HTT 補題 2.4.6.4*　単射な圏同値の厳密なレトラクション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=155)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体的集合の包含 $`\mathcal C\subseteq\mathcal D` が圏同値で $`\mathcal C` が ∞ 圏なら、この包含には単体的レトラクションがある。

KB-W2原文・型再照合：仮定：単射な圏同値と始域の準圏性（Lean が強い：終域にも準圏性を要求）。結論：元の包含の厳密な左逆を与える（一致）。

結論は同値の逆関手をホモトピーまで選ぶことより強く、$`\mathcal C` への制限が厳密に恒等となる写像を要求する。内角を埋められる $`\mathcal C` を値域として持ち上げを使う。

:::

# 2.4.7 Bifibrations

%%%
number := false
tag := "htt-2-4-7"
%%%

:::proposition "htt_2_4_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isQCatEquivalence_of_rightFibration_fibers")
*HTT 命題 2.4.7.6*　両側ファイブレーションの繊維同値判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=158)）。対応表の状態：一部（stronger-hyp）。

*主張*　同じ積の底 $`S\times T` 上の二つの bifibration の間の射が各頂点ファイバーのホモトピー同値を誘導するなら、全空間の圏同値である。

KB-W2原文・型再照合：仮定：元の二つの射影をさらに RightFibration とし、積の底と全空間を準圏に限定（Lean が強い）。結論：同じ底 S×T 上の f の各 vertexFiberMap の同値から f の IsQCatEquivalence を得る。原典の同じ結論はこの追加仮定下で直接得るが、任意 bifibration から RightFibration を導くとは主張しない。

左右の底方向に異なる持ち上げ性質を使う構成でも、固定した両端のファイバーは空間になる。点ごとの比較をその二方向の持ち上げと合わせて全空間に移す。

:::

:::proposition "htt_2_4_7_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.isQCatEquivalence")
*HTT 命題 2.4.7.7*　両因子の圏同値に沿う底変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=159)）。対応表の状態：一部（stronger-hyp）。

*主張*　bifibration を二つの底因子それぞれの圏同値に沿って引き戻すと、引き戻した全空間から元の全空間への射は圏同値である。

KB-W2原文・型再照合：仮定：元の bifibration p に EquivalenceLifting p、全空間の準圏性、積の base-change map の native QCatEquivalence を追加（Lean が強い）。結論：同じ X′→X は IsPrecompositionEquivalence となり、引戻しを含む両側の準圏性から IsQCatEquivalence を得る。bifibration と f,g の仮定だけからこれらの追加条件を導く部分は含まない。

底を一方ずつ替えても、引き戻し後のファイバーは対応する元のファイバーを保つ。結果は積の底全体にわたる比較を述べる。

:::

:::proposition "htt_2_4_7_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.exists_strict_retraction")
*HTT 命題 2.4.7.9*　両側ファイブレーション上の厳密なレトラクション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=160)）。対応表の状態：一部（stronger-hyp）。

*主張*　積の底上の bifibration の間の点ごとの同値が余ファイブレーションでもあるとき、底上でその厳密なレトラクションが存在する。

KB-W2原文・型再照合：仮定：元の単射 p に全空間の準圏性と native IsQCatEquivalence p を追加（Lean が強い）。結論：同じ underlying simplicial p に対して r:Y→X と p≫r=id を得る。この left-inverse の成分に一致するが、元の bifibration/fiberwise 仮定だけから追加同値を導く比較と、r が S×T 上の map である性質は含まない。

レトラクションは底への可換性を保ち、元の射と合成すると始域で恒等になる。底を忘れた圏同値から任意の逆を選ぶだけではこの等式は得られない。

:::

:::corollary "htt_2_4_7_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_innerFibration") (uses := "htt_1_1_2_4")
*HTT 系 2.4.7.11*　矢印準圏からの両端評価（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=161)）。対応表の状態：一部（component）。

*主張*　∞ 圏 $`\mathcal C` の矢印 ∞ 圏 $`\operatorname{Fun}(\Delta^1,\mathcal C)` から二端点への評価は bifibration である。

KB-W2原文・型再照合：仮定：準圏 C（HTT と一致）。結論：同じ arrowEndpointPair:Fun(Δ1,C)→C×C が InnerFibration であり、bifibration の定義の最初の明示条件に一致する。残る二つの条件付き outer-horn filling は含まず、EquivalenceLifting の別条件をその代用にはしない。

端点の片方を動かす操作は後合成、もう一方を動かす操作は前合成として働く。二端点を固定したファイバーは、対応する対象間の写像空間になる。

:::

:::corollary "htt_2_4_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource_innerFibration, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_cartesian_unitComma_lift, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isCartesianEdge_unitCommaSource_of_target") (uses := "htt_1_1_2_4, htt_2_4_2_1, htt_2_4_7_11")
*HTT 系 2.4.7.12*　comma の始域射影と Cartesian 辺（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=161)）。対応表の状態：一部（component）。

*主張*　$`f:\mathcal C\to\mathcal D` に対し、$`\mathcal D` の矢印の終点を $`f` で引き戻したコンマ ∞ 圏から始点への射影は Cartesian ファイブレーションで、Cartesian 辺は $`\mathcal C` への像が同値である辺である。

KB-W2原文・型再照合：仮定：準圏間の G:Y→X（HTT と一致）。結論：unitCommaSource は同じ Fun(Δ1,X)×Fun(\{1\},X)Y の始端射影であり、innerFibration と全ての指定終点の Cartesian lifts は CartesianFibration の構造を与える。また Y への像が可逆なら Cartesian。原典の最初の assertion と iff の十分方向に一致し、必要方向は含まない。

対象は $`d\to f(c)` という向きの矢印である。始点を変える持ち上げは前合成で与えられ、Cartesian 性には終点を指定する $`c` 側の変化が同値であることが必要になる。

:::

