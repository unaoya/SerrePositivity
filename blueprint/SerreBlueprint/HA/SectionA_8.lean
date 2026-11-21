-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.8 Digression: Recollement" =>
%%%
number := false
tag := "ha-A-8"
%%%

HA A.8 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_8_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits")
*HA 定義 A.8.6*　Digression: Recollement (p. 1445)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1445)）。対応表の状態：一部（component）。

*主張*　左完全な対応とは、$`\Delta^1` 上のデカルト・ファイブレーションで、両ファイバーが有限極限を持ち、終点から始点への移送が有限極限を保つものである。

同じ対応p:M→Δ¹についてCartesianFibrationは条件(ii)そのもの。各fiberの有限極限はHasFiniteLimitsで表す。分類される関手のleft exact性は含まない。

デカルト辺で定まる分類関手の向きは $`M_1\to M_0` である。左完全性を検査するのはこの関手である。

:::

