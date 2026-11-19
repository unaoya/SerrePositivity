import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 3.2 Straightening and Unstraightening" =>
%%%
number := false
tag := "htt-3-2"
%%%

HTT 3.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 3.2.2 Cartesian Fibrations over a Simplex

%%%
number := false
tag := "htt-3-2-2"
%%%

:::corollary "htt_3_2_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.ihom_map_leftFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_cocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration") (uses := "htt_2_4_1_1, htt_2_4_2_1")
*HTT 系 3.2.2.12*　相対指数の余カルテジアン性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=203)）。対応表の状態：一部（special）。

*主張*　Cartesian ファイブレーション $`X\to S` による相対指数を余 Cartesian ファイブレーション $`Y\to Z` に施すと余 Cartesian ファイブレーションになり、その余 Cartesian 辺は $`X` の Cartesian 辺を $`Y` の余 Cartesian 辺へ送ることで判定される。

KB-W2原文・型再照合：仮定：p:X→S は Cartesian、q:Y→Z は cocartesian（Lean が強い：S=Δ⁰、q を left fibration に限定）。結論：この場合は Y′=Fun(X,Y),Z′=Fun(X,Z) と取れ、q′ が left、従って cocartesian fibration となる。全 Y と Y′ の辺が cocartesian なので (2) の辺の条件も両側が成立し一致。一般の相対 q には拡張しない。

相対指数の $`K` からの点は、$`X\times_S K` を始域とする写像で表す。こうして一つの辺を $`X` 付きの写像として読むと、端点の比較だけでなく指定された Cartesian な脚の像を検査できる。

:::

# 3.2.5 The Relative Nerve

%%%
number := false
tag := "htt-3-2-5"
%%%

:::definition "htt_3_2_5_9" (lean := "SSet.opFunctor")
*HTT 記法 3.2.5.9*　図式を点ごとに反転する記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=215)）。対応表の状態：一部（component）。

*主張*　通常圏 $`\mathcal C` 上の単体的集合の図式 $`f` に、各値に反対化を施す図式 $`f^{\mathrm{op}}` を対応させ、標識付きの場合も同様に記す。

KB-W2原文・型再照合：仮定：通常圏 C と f:C→SSet（HTT と一致）。結論：f⋙SSet.opFunctor が同じ C を始域とし c↦f(c)op を与えるという unmarked diagram の部分は一致。marked SSet 値の場合の marking の反転の定義は含まない。

反転するのは各値の単体の向きである。その操作は単体的写像に対して関手的なので、添字圏 $`\mathcal C` の射の向きはそのままにできる。

:::

