import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA A.9 Exit Paths and Constructible Sheaves" =>
%%%
number := false
tag := "ha-A-9"
%%%

HA A.9 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_A_9_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex")
*HA 構成 A.9.2*　exit path 上の left fibration から Ψ の構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1457)）。対応表の状態：一部（component）。

*主張*　成層空間の exit-path 単体集合上の左ファイブレーション $`Y` は、開 $`F_\sigma` 集合 $`U` に $`\operatorname{Fun}_{\operatorname{Sing}_A(X)}(\operatorname{Sing}_A(U),Y)` を割り当てる空間値前層を定める。

KB-W2原文・型再照合：仮定：p:Y→SingA(X)をleft fibration、a:SingA(U)→SingA(X)を指定（HAのfibrant入力の単体的条件に一致）。結論：底上のrelativeFunctorSpaceを定め、その値がKan complexとなる（θ(U,Y)の式とKan性に一致する部分）。位相的SingAの構成、全(U,Y)でのfunctoriality、covariant model structureとcoherent nerve、およびΨX全体の構成は含まれない。

共変モデル構造のファイブラント対象に制限すると各値が Kan 複体になる。$`U` について制限、$`Y` について合成があり、これらを nerve に移して前層圏への $`\Psi_X` を作る。

:::

