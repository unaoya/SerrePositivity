-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.6 ∞-Categories of Exit Paths" =>
%%%
number := false
tag := "ha-A-6"
%%%

HA A.6 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_6_6" (lean := "PreAbstractSimplicialComplex")
*HA 定義 A.6.6*　抽象単体複体・局所有限性・実現（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1434)）。対応表の状態：一部（component）。

*主張*　抽象単体複体は頂点集合と、空でない部分集合を取る操作で閉じた有限非空頂点集合の族からなる。

KB-W2原文・型再照合：仮定：頂点の型V（HAと一致）。結論：非空有限部分集合の下方閉族をfacesとして持つ抽象単体複体のデータを定義する（(1)(2)に一致する部分）。locally finiteの専用述語、線形順序を選んだ単体集合とその実現、重み付き点による全表示は含まれない。

局所有限性は各単体を含む単体が有限個であることをいう。頂点を全順序化すると単体集合を作れ、その実現は指定の単体に台を持つ総和一の非負重みで表せる。順序の選択を変えてもこの実現は標準的に同相である。

:::

