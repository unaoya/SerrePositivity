import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Category.Pointed

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 2 ∞-Operads" =>
%%%
number := false
tag := "ha-2"
%%%

HA 2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_2_0_0_2" (lean := "typeToPointed")
*HA 記法 2.0.0.2*　∞-Operads (p. 165)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=165)）。対応表の状態：一部（component）。

*主張*　$`\mathrm{Fin}_*` は $`\langle n\rangle=\{*,1,\ldots,n\}` と基点保存写像の圏で、$`\rho^i:\langle n\rangle\to\langle1\rangle` は $`i` だけを非基点に送る。

KB-W2型再照合：仮定：型 I（Lean が弱い：有限性を要求しない）。結論：Option I に none を基点として付加する I∗ の構成（一致する成分。Fin∗ の骨格と各 ρᵢ は型に含まれない）。

任意の有限集合に基点を添加できる。ここでは各濃度の代表を取り、基点以外の各位置を一本ずつ抜き出す写像に $`\rho^i` の記号を使う。

:::

