-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Topology.Sets.Opens

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 6.4 n-Topoi" =>
%%%
number := false
tag := "htt-6-4"
%%%

HTT 6.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.4.2 0-Topoi and Locales

%%%
number := false
tag := "htt-6-4-2"
%%%

:::definition "htt_6_4_2_3" (lean := "Order.Frame, Order.Frame.ofMinimalAxioms, inf_sSup_eq, Locale.of")
*HTT 定義 6.4.2.3*　ロケールの順序公理による定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=661)）。対応表の状態：Mathlib にある。

*主張*　ロケールとは任意の上限を持つ半順序集合で、固定元との交わりが任意の上限に分配するものである。

仮定：半順序 U（HTT と一致）。結論：complete lattice と meet の任意 join に対する分配律による locale は一致。Frame の Heyting 操作は ofMinimalAxioms がこの公理だけから回収し、余分な存在仮定ではない。Locale.of はその同じ台集合を束縛する。

一般の完備束に対し、有限交わりと任意和の相互作用を追加した定義である。二元の交わりは下界全体の上限として得られる。

:::

:::proposition "htt_6_4_2_4" (lean := "TopologicalSpace.Opens.instFrame, topToLocale, Locale.pt, Locale.adjunctionTopToLocalePT")
*HTT 例 6.4.2.4*　開集合のロケールと点との随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=661)）。対応表の状態：一部（component）。

*主張*　位相空間から開集合のロケールを、ロケールから素フィルターの空間を作る随伴は、空間的ロケールと sober 空間の同値を与える。

KB-W2原文・型再照合：仮定：位相空間 X と locale U（HTT と一致）。結論：開集合が locale を成し、locale の点に自然な位相を入れ、空間から locale への関手と点関手が随伴となる部分は一致。spatial locales と sober spaces への制限での同値の全主張は含まない。

開集合は任意和と有限交わりでロケールをなす。逆に開集合に当たる束から点を回復する操作は一般に情報を落とし得るので、同値は両側の指定された部分圏で述べられる。

:::

