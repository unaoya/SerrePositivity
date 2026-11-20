-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
import SerrePositivity.KST.Comparison.FibrantPullbackComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 2.3 Disintegration and Assembly" =>
%%%
number := false
tag := "ha-2-3"
%%%

HA 2.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.3.3 Approximations to ∞-Operads

%%%
number := false
tag := "ha-2-3-3"
%%%

:::lemma_ "ha_2_3_3_13" (lean := "SerrePositivity.KST.Comparison.isHomotopyPullback_of_fibration")
*HA 補題 2.3.3.13*　Approximations to ∞-Operads (p. 262)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=262)）。対応表の状態：一部（special）。

*主張*　Kan 複体上の圏論的ファイブレーションの頂点での厳密なファイバーは、Kan モデル構造でのホモトピーファイバーを表す。

KB-W2型再照合：仮定：単体集合の引き戻し四角形と右辺が Kan ファイブレーション（Lean が強い：HA の categorical fibration を Kan に限定。底の Kan 性は不要）。結論：標準比較が anodyne 局所化で可逆なホモトピー引き戻し（頂点への引き戻しで HA の結論に一致）。

主張はファイバーを定める引き戻し四角形についてである。全体とファイバーは準圏でよく、底を Kan 複体と仮定する。

:::

:::definition "ha_2_3_3_28" (lean := "SSet.InnerFibration")
*HA 定義 2.3.3.28*　Approximations to ∞-Operads (p. 269)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=269)）。対応表の状態：一部（component）。

*主張*　オペラッドの近似 $`E` 上の写像が fibrous であるには、内ファイブレーション、慣性辺の余デカルト持ち上げ、指定の相対積、ファイバーの積分解の四条件を課す。

原文のfibrous条件(1)は同じqのinner fibration性であり、InnerFibration qの型と一致する。inert辺の持ち上げ・相対積・fiberの比較という他の条件は含まない。

$`\rho^i` を覆う慣性辺を持ち上げると、全体の対象はその各終点の相対積を表す。さらに底の対象を固定したファイバーも、それらの色のファイバーの積に同値である。

:::

:::proposition "ha_2_3_3_29" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_of_isCocartesianEdge")
*HA 注意 2.3.3.29*　Approximations to ∞-Operads (p. 270)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=270)）。対応表の状態：一部（stronger-hyp）。

*主張*　fibrous の定義のうち、内ファイブレーションと慣性辺を余デカルトに持ち上げる条件から、圏論的ファイブレーションであることが従う。

KB-W2型再照合：仮定：準圏間の inner fibration と同値辺の持ち上げ（Lean は可逆辺の持ち上げを直接入力。余デカルト持ち上げは底の辺が可逆なら可逆となる）。結論：単射な前合成同値に対する持ち上げ性（categorical fibration の結論に一致）。f-inert に可逆辺が含まれる operadic 条件は型に含まれない。

底の同値は慣性辺として扱えるため、持ち上げ条件をここに適用する。残り二つの積の条件はこの結論には使わない。

:::

# 2.3.4 Disintegration of ∞-Operads

%%%
number := false
tag := "ha-2-3-4"
%%%

:::lemma_ "ha_2_3_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration")
*HA 補題 2.3.4.6*　Disintegration of ∞-Operads (p. 277)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=277)）。対応表の状態：一部（special）。

*主張*　終域が Kan 複体である単体集合の弱ホモトピー同値は左共終である。

KB-W2型再照合：仮定：単体集合の射が自明 Kan ファイブレーション（Lean が強い：弱ホモトピー同値のうち自明 Kan の場合。底の Kan 性は要求しない）。結論：左共終性（その場合に HA と一致）。

終域を空間とみなせることが仮定である。この場合、弱ホモトピー型を保つ写像から共終性が得られる。

:::

:::lemma_ "ha_2_3_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal")
*HA 補題 2.3.4.7*　Disintegration of ∞-Operads (p. 277)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=277)）。対応表の状態：一部（special）。

*主張*　図式 $`Y\to C` がすべての辺を同値に送り余極限余錐を持つとき、弱ホモトピー同値 $`X\to Y` に沿って制限した余錐も余極限余錐である。

KB-W2型再照合：仮定：準圏内の余極限余錐と添字への自明 Kan ファイブレーション（Lean が強い：弱ホモトピー同値を自明 Kan に限定。図式の辺が同値であることは要求しない）。結論：引き戻した余錐の余極限性（その場合に HA と一致）。

制限では余錐の頂点を変えない。図式が同値だけを使うことによって、添字単体集合の弱ホモトピー型の比較を余極限の普遍性に移せる。

:::

