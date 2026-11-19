import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.Order.Heyting.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.SmallInductiveDimension
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 7.2 Dimension Theory" =>
%%%
number := false
tag := "htt-7-2"
%%%

HTT 7.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.2.2 Cohomological Dimension

%%%
number := false
tag := "htt-7-2-2"
%%%

:::proposition "htt_7_2_2_2" (lean := "CategoryTheory.GrpObj, CategoryTheory.Hom.group, CategoryTheory.yonedaGrpObj, CategoryTheory.GrpObj.ofRepresentableBy")
*HTT 例 7.2.2.2*　通常圏の内部群と群値表現可能関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=743)）。対応表の状態：一部（component）。

*主張*　有限極限を持つ通常圏での内部群は、各対象からの Hom に自然な群構造を入れたものと言い換えられ、内部群の圏の nerve は元の圏の nerve における群対象の ∞ 圏に同値である。

KB-W2原文・型再照合：仮定：有限積を持つ通常圏 C を CartesianMonoidalCategory として扱う（原典の通常圏部分と一致）。結論：単位・乗法・逆射を持つ内部群と、Hom(-,X) に自然な群構造を入れる群値表現可能前層の二つの表示は一致。N(Grp(C)) と準圏 N(C) の simplicial group objects の同値は未比較。

積を表現する普遍性により、通常の単位・反転・積の演算は試験対象からの写像集合に移る。逆に群演算が試験対象について自然なら、それを表現する射として内部演算を回復できる。

:::

:::definition "htt_7_2_2_7" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex")
*HTT 定義 7.2.2.7*　零対象を定める二つの条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=743)）。対応表の状態：本体にある。

*主張*　∞ 圏の零対象とは、始対象でも終対象でもある対象である。

仮定：準圏 X の頂点 z（Lean は単体集合まで弱い）。結論：IsZeroVertex z は IsInitialVertex z∧IsTerminalVertex z そのもので、原典の零対象の定義と一致。

同じ対象に向かう写像空間と、そこから出る写像空間の両方が、任意の相手について可縮である。零射はこの対象を経由する。

:::

# 7.2.3 Covering Dimension

%%%
number := false
tag := "htt-7-2-3"
%%%

:::proposition "htt_7_2_3_4" (lean := "HasSmallInductiveDimensionLE")
*HTT 注意 7.2.3.4*　小帰納次元の再帰的な定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=756)）。対応表の状態：一部（component）。

*主張*　小・大帰納次元は、それぞれ点・閉集合の開近傍の境界を低次元とする再帰的な次元で、可分距離空間では被覆次元とも一致する。

KB-W2原文・型再照合：仮定：任意の位相空間 X と自然数 n（HTT の小帰納次元の部分と一致）。結論：境界の次元が n 未満の開集合からなる基底を持つという再帰的な small inductive dimension の定義は一致。large inductive dimension、可分距離空間での covering dimension との一致は含まない。

近傍を任意に小さく取れるという部分が、元の空間の局所的な境界の複雑さを測る。被覆の多重度で測る次元との一致には空間への仮定があり、一般の定義としては区別する。

:::

# 7.2.4 Heyting Dimension

%%%
number := false
tag := "htt-7-2-4"
%%%

:::proposition "htt_7_2_4_1" (lean := "le_himp_iff'")
*HTT 注意 7.2.4.1*　Heyting 空間と Heyting 代数の双対性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=760)）。対応表の状態：一部（component）。

*主張*　任意の $`x,y` に対して $`x\wedge z\le y` を満たす最大の $`z` を持つ分配束を Heyting 代数といい、sober な Heyting 空間のコンパクト開集合の束との間に双対性がある。

原文冒頭の通常のHeyting代数の回想について、le\_himp\_iff′ は x∧z≤y を満たす最大元 x⇨y の普遍性を直接述べる。後半のcompact openのHeyting構造・spectrumによる双対性は含まない。

最大の $`z` は交わりに対する含意の役割を果たす。空間側ではコンパクト開集合だけでこの演算を行えることが必要で、sober 条件によって束のスペクトルから空間を回復できる。

:::

:::proposition "htt_7_2_4_2" (lean := "TopologicalSpace.NoetherianSpace.isCompact")
*HTT 注意 7.2.4.2*　ネーター空間の開集合のコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=760)）。対応表の状態：一部（component）。

*主張*　Noether 位相空間はすべての開集合がコンパクトなので、Heyting 空間である。

KB-W2原文・型再照合：仮定：Noetherian な位相空間 X（HTT と一致）。結論：全ての部分集合、特に全ての開集合がコンパクト（本文に明記された結論と一致、結論の一部）。原典の HeytingSpace の述語はなく、その三つの条件を束ねた instance にはしていない。

開集合の中からコンパクトなものを選び分ける必要がない。そのため開集合の束で使う演算をコンパクト開集合の束でも使える。

:::

