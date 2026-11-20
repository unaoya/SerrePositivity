-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.RingTheory.Kaehler.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 7.4 Deformation Theory" =>
%%%
number := false
tag := "ha-7-4"
%%%

HA 7.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.4.3 Connectivity and Finiteness of the Cotangent Complex

%%%
number := false
tag := "ha-7-4-3"
%%%

:::proposition "ha_7_4_3_7" (lean := "KaehlerDifferential.exact_mapBaseChange_map, KaehlerDifferential.map_surjective")
*HA 注意 7.4.3.7*　Connectivity and Finiteness of the Cotangent Complex (p. 1361)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1361)）。対応表の状態：Mathlib にある。

*主張*　可換環の射 $`R'\to R` に対して、$`R\otimes_{R'}\Omega_{R'}\to\Omega_R\to\Omega_{R/R'}\to0` は完全である。

仮定：通常可換環 R₀→R（HA と一致。底環を ℤ とする）。結論：R⊗R₀ ΩR₀→ΩR→ΩR/R₀→0 の完全性と末射の全射性を与える（HA の Tor₀ による右完全列と一致）。

絶対微分 $`\Omega_R` から $`R'` の元の微分の像が生成する部分加群を除くと、相対微分を得る。原典の先頭項の $`\operatorname{Tor}^{R'}_0` はテンソル積であり、先頭の比較射の単射性は一般には要求されない。

:::

