import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTrivialComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 3.1 Free Algebras" =>
%%%
number := false
tag := "ha-3-1"
%%%

HA 3.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 3.1.1 Operadic Colimit Diagrams

%%%
number := false
tag := "ha-3-1-1"
%%%

:::proposition "ha_3_1_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence") (uses := "htt_2_0_0_3, htt_2_1_2_1, htt_2_4_4_6")
*HA 注意 3.1.1.5*　Operadic Colimit Diagrams (p. 319)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=319)）。対応表の状態：一部（direction）。

*主張*　弱オペラッド的相対余極限を定義する比較 $`\psi` は常に左ファイブレーションであり、自明 Kan ファイブレーションであることは圏論的同値であることで判定できる。

KB-W2型再照合：仮定：準圏間の左ファイブレーションが準圏同値である（Lean は ψ という指定を外し、左ファイブレーション性を仮定）。結論：自明 Kan ファイブレーションになる（ψ に関する同値判定の一方向に一致）。ψ の左ファイブレーション性は型に含まれない。

活性な余錐に制限した下の圏から、通常の下の圏と底の活性な余錐を合わせた引き戻しへの比較である。この射に左ファイブレーションの同値判定を適用する。

:::

