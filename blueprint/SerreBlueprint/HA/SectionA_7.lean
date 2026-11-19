import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.7 A Seifert-van Kampen Theorem for Exit Paths" =>
%%%
number := false
tag := "ha-A-7"
%%%

HA A.7 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_7_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
*HA 定義 A.7.3*　stratum chain を固定した exit-path 図式空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1436)）。対応表の状態：一部（component）。

*主張*　成層空間の exit-path 単体集合において、層の指定鎖 $`a_0\le\cdots\le a_n` に従う図式の単体集合は、$`\Delta^n` からの関手をその鎖の上で取ったファイバーである。

KB-W2原文・型再照合：仮定：p:E→N(A)をexit-path射影の入力模型として指定し、chain aを∆n→N(A)で与える（HAの式の入力に一致）。結論：内部Homからchainの点へのfiberでFun\_\{N(A)\}(∆n,E)を構成する（SingA(X)\[a\]の表示に一致）。位相空間からのE=SingA(X)自体の構成は含まれない。

$`\operatorname{Fun}(\Delta^n,\operatorname{Sing}_A(X))` を $`\operatorname{Fun}(\Delta^n,N(A))` に写し、指定の鎖が定める頂点との引き戻しを取る。

:::

:::proposition "ha_A_7_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex")
*HA 注意 A.7.4*　stratum chain を固定した図式空間の Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1437)）。対応表の状態：一部（stronger-hyp）。

*主張*　円錐的 $`A` 成層空間では、層の各指定鎖上の exit-path 図式の単体集合は Kan 複体である。

KB-W2原文・型再照合：仮定：p:E→N(A)がleft fibrationである場合に限定（Leanが強い：HAのinner fibrationに代えてleft fibrationを追加）。結論：任意∆n→N(A)上のrelativeFunctorSpaceはKan complex（表示された固定chainのfiberのKan性に一致）。conicalなXからSingAを構成し一般inner fibrationの場合にも適用する比較は含まれない。

成層の特異複体に関する A.6.4 の性質を、指定の鎖を覆う図式へのファイバーに適用する。

:::

