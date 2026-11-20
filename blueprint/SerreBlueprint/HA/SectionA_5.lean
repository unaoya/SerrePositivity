-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Order.WellFounded
import Mathlib.Topology.Order.UpperLowerSetTopology

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.5 Constructible Sheaves" =>
%%%
number := false
tag := "ha-A-5"
%%%

HA A.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_5_1" (lean := "Topology.upperSet")
*HA 定義 A.5.1*　upper-set 位相と poset による stratification（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1421)）。対応表の状態：一部（component）。

*主張*　半順序集合 $`A` に上方閉集合を開集合とする位相を入れたとき、空間 $`X` の $`A` 成層とは連続写像 $`X\to A` である。

KB-W2原文・型再照合：仮定：半順序集合A（HAと一致）。結論：開集合を上方閉集合とするAlexandrov位相を与える（冒頭の位相の定義に一致）。任意Xからの連続写像にstratificationという名を与える専用型と五つのstratumの族は含まれない。

点 $`a` のファイバーを $`X_a` と書く。$`X_{\le a},X_{<a},X_{\ge a},X_{>a}` は対応する順序部分集合の逆像を表す。

:::

:::definition "ha_A_5_7" (lean := "WellFounded.wellFounded_iff_has_min")
*HA 定義 A.5.7*　半順序集合の昇鎖条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1422)）。対応表の状態：Mathlib にある。

*主張*　半順序集合が昇鎖条件を満たすとは、任意の非空部分集合が極大元を持つことである。

仮定：半順序集合Aにr(b,a):=a\<bという逆の厳密順序を入れる（HAと一致）。結論：rがwell-foundedであることと全非空部分集合に極大元があることが同値（定義されたACCそのものを表す）。

極大元は、部分集合内で真に上にある元が存在しない元である。互いに比較できない極大元が複数あってもよい。

:::

:::proposition "ha_A_5_8" (lean := "WellFounded.wellFounded_iff_has_min, wellFounded_iff_isEmpty_descending_chain")
*HA 注意 A.5.8*　昇鎖条件と無限上昇列の非存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1422)）。対応表の状態：Mathlib にある。

*主張*　昇鎖条件は、真に増大し続ける無限列 $`a_0<a_1<\cdots` が存在しないことと同値である。

仮定：半順序集合A、r(b,a):=a\<b（HAと一致）。結論：全非空部分集合に極大元があることと無限列a(n)\<a(n+1)が存在しないことが同値（原典の同値に一致）。

その列の像には極大元がない。逆に極大元のない非空部分集合で順に真に上の元を選ぶと、無限昇鎖を得る。

:::

