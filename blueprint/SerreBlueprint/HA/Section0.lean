import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 0 序論" =>
%%%
number := false
tag := "ha-0"
%%%

HA 0 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_0_0_0_1" (lean := "SSet.Quasicategory")
*HA 定義 0.0.0.1*　内角充填条件による ∞ 圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=11)）。対応表の状態：Mathlib にある。

*主張*　∞ 圏とは、単体的集合 $`\mathcal C` であって $`0<i<n` の角 $`\Lambda_i^n\to\mathcal C` が常に $`\Delta^n` へ延びるものをいう。

仮定：単体集合 C（HA と一致）。結論：全内ホーン 0\<i\<n の充填条件で準圏を定義する（HA と一致。定義では n≥2 として空虚な低次を省く）。

二次元では二本の接続した辺を三角形に補う条件になる。通常圏の nerve の場合に比べ、充填の存在は要求するが、その一意性は要求しない。

:::

:::proposition "ha_0_0_0_2" (lean := "CategoryTheory.Nerve.quasicategory")
*HA 注意 0.0.0.2*　弱 Kan 複体と準圏の呼称（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=11)）。対応表の状態：一部（component）。

*主張*　この内角条件を満たす単体的集合は弱 Kan 複体または準圏とも呼ばれ、通常圏の nerve はその例である。

KB-W2型再照合：通常圏Eのnerveが準圏であるという原文の同じ数学的成分を、Nerve.quasicategoryの型が直接返す。weak Kanという歴史的呼称と文献紹介は含まない。

弱 Kan という名は内側の角に限る点を表す。通常圏の合成を再現する模型なので、随伴、極限、層などもこの枠に移して考えられる。

:::

