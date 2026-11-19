import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.4 Singular Shape" =>
%%%
number := false
tag := "ha-A-4"
%%%

HA A.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_4_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
*HA 構成 A.4.17*　Sing 上の Kan fibration から層への Ψ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1420)）。対応表の状態：一部（component）。

*主張*　$`\operatorname{Sing}(X)` 上の Kan ファイブレーション $`Y` に、開集合 $`U` ごとの空間 $`\operatorname{Fun}_{\operatorname{Sing}(X)}(\operatorname{Sing}(U),Y)` を対応させると、$`X` 上の層を得る。

KB-W2原文・型再照合：仮定：Y→Sing(X)とSing(U)→Sing(X)を指定（HAの入力に一致する単体集合模型）。結論：底上の全単体的写像空間Fun\_SingX(Sing(U),Y)をinternal Homのfiberで構成する（θ(U,Y)の値の式に一致する部分）。θ全体の関手性、モデル圏のfibrant-cofibrant比較、層条件、ΨXとその全nerveの構成は含まれない。

通常のスライスモデル構造のファイブラントかつ余ファイブラントな対象に制限して nerve を取る。開集合の包含には制限で反変に対応し、Seifert–van Kampen の比較により前層が層条件を満たす。

:::

