import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.4 The Relative Tensor Product" =>
%%%
number := false
tag := "ha-4-4"
%%%

HA 4.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.4.3 Associativity of the Tensor Product

%%%
number := false
tag := "ha-4-4-3"
%%%

:::definition "ha_4_4_3_7"
*HA 記法 4.4.3.7*　Associativity of the Tensor Product (p. 582)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=582)）。対応表の状態：一部（component）。

*主張*　面写像 $`\alpha^i:[m-1]\hookrightarrow[m]` は $`i` を飛ばし、内側の面では隣接する二頂点を三頂点の区間に入れる図式が一般化 ∞ オペラッドの比較を定める。

KB-W2型再照合：仮定：有限順序集合 \[m\] と省く添字 i（Lean が強い：単体圏の部分に限る）。結論：i を飛ばす単調単射を i 番目の面写像として構成する（αᵢ の成分に一致）。Tens 間の ξ は含まれない。

$`0<i<m` のとき、$`[m-1]` の区間 $`\{i-1,i\}` の像は $`[m]` の区間 $`\{i-1,i,i+1\}` の両端である。この同定による可換四角形から原典の $`\xi` を得る。

宣言：`SimplexCategory.δ`、`SimplexCategory.coe_δ`

:::

