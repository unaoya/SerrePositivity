import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.3 The Seifert-van Kampen Theorem" =>
%%%
number := false
tag := "ha-A-3"
%%%

HA A.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_3_6" (lean := "SimplexCategory.sd, SSet.sd, SSet.sdExAdjunction")
*HA 記法 A.3.6*　細分 functor とその mapping cylinder（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1414)）。対応表の状態：一部（component）。

*主張*　非空部分集合の包含順序の nerve は単体の重心細分を与え、その順序と元の頂点順序を合わせて作る細分の円筒は、実現すると元の単体集合の実現と区間の積になる。

KB-W2原文・型再照合：仮定：単体集合Kと各有限順序\[n\]（HAと一致）。結論：非空有限鎖（\[n\]では非空部分集合）のnerveからsdを左Kan延長で構成し、exとの随伴からsdが余極限を保つ（最初の細分functorの構成に一致する部分）。拡大posetによるsd-barとその実現の実現(K)×\[0,1\]への同相、両端の貼込みは含まれない。

二つの順序の間では、部分集合 $`\sigma` の全頂点が $`i` 以下なら $`\sigma\le i` と置く。実現で元の頂点を高さ $`0`、部分集合の重心を高さ $`1` に置く。この構成は単体に自然で、余極限で一般の単体集合に延ばせる。

:::

