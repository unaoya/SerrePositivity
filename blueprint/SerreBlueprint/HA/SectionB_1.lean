-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA B.1 𝔓-Anodyne Morphisms" =>
%%%
number := false
tag := "ha-B-1"
%%%

HA B.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::lemma_ "ha_B_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting")
*HA 補題 B.1.7*　局所 coCartesian 辺による最初の外側 horn の充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1471)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\Delta^n` 上の内ファイブレーションで、外角 $`\Lambda^n_0` の指定の辺 $`0\to1` が $`\{0,1,n\}` 上で局所余デカルトなら、角の持ち上げは全単体に延びる。

KB-W2原文・型再照合：仮定：p:X→∆nと外側hornの先頭辺を指定し、その辺がX全体でp-coCartesianのhorn liftingを持つ（Leanが強い：局所∆\{0,1,n\}での条件を全体のcoCartesian条件に強める）。結論：同じ底上で外側hornを充填する∆n→Xが存在（原典の延長の結論に一致）。局所triangleでのcoCartesian性だけからこの全体条件を導く部分は含まれない。

$`n\ge2` とし、底への写像は恒等のまま固定する。条件は $`0,1,n` に制限したファイブレーションでの持ち上げの性質である。

:::

