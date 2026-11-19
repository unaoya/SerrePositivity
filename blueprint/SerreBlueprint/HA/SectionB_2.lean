import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA B.2 The Model Structure on (Set_Δ^+)_/𝔓" =>
%%%
number := false
tag := "ha-B-2"
%%%

HA B.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::lemma_ "ha_B_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers")
*HA 補題 B.2.4*　P 同値・homotopy 逆・fiber ごとの同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1483)）。対応表の状態：一部（stronger-hyp）。

*主張*　圏論的パターンに従うファイバー対象の間では、パターン同値、印付きホモトピー逆の存在、底の各辺上での同値が同値である。

KB-W2原文・型再照合：仮定：X→S・Y→Sがleft fibrationであり全空間が準圏、fが底上で全頂点fiberの圏同値を誘導（Leanが強い：一般P-fiberedよりleft fibrationに限定）。結論：全空間のfは圏同値であり、この判定を∆1への引き戻しにも使える（(3′)から各辺上の圏同値(3)を得る方向のleft-fibrationの場合）。P-equivalenceとmarkedなhomotopy逆の全iffは含まれない。

印付き区間で逆の合成と恒等射を結ぶ。底の全辺が印付きの場合、各辺上での判定は各頂点のファイバーでの同値の判定に簡約できる。

:::

