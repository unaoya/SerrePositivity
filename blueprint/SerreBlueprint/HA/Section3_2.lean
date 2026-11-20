-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 3.2 Limits and Colimits of Algebras" =>
%%%
number := false
tag := "ha-3-2"
%%%

HA 3.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 3.2.2 Limits of Algebras

%%%
number := false
tag := "ha-3-2-2"
%%%

:::lemma_ "ha_3_2_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_pointwise_of_hasPointwiseLimits") (uses := "htt_1_1_2_4, htt_1_2_13_4, htt_4_3_2_13")
*HA 補題 3.2.2.9*　Limits of Algebras (p. 362)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=362)）。対応表の状態：一部（special）。

*主張*　準圏の圏論的ファイブレーションに関して、各点で相対極限錐が指定の底の上に存在すれば、それらを図式の族として取れる。族の相対極限性は各点で判定できる。

KB-W2型再照合：仮定：任意の二つの単体集合を図式・パラメーターとし、準圏 X で全評価図式が極限を持つ（Lean が強い：底 D が終準圏の場合に限る）。結論：点ごとの極限錐が自然な族に延長でき、関手 ∞ 圏の極限性が点ごとの極限性と同値（一致する絶対極限の特殊例）。

底の図式を $`K^{\triangleleft}\times E` 上で固定する。得た族を $`K^{\triangleleft}\to\operatorname{Fun}(E,C)` に随伴で移すと、合成から得る $`\operatorname{Fun}(E,C)\to\operatorname{Fun}(E,D)` に関する極限錐になる。

:::

