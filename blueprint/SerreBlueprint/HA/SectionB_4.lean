-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Adjunction.Basic
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.SSetPullbackAdjoint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomCartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseHom

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA B.4 Functoriality" =>
%%%
number := false
tag := "ha-B-4"
%%%

HA B.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_B_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalSSetPullback_isLeftAdjoint, CategoryTheory.Adjunction.ofIsLeftAdjoint")
*HA 記法 B.4.4*　単体集合上の依存積の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1509)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`\pi:Y\to Z` によるスライスの引き戻しは右随伴 $`\pi_*` を持ち、$`Z` 上の $`K\to\pi_*X` が $`Y` 上の $`K\times_ZY\to X` に自然に対応する。

仮定：任意の単体集合の射π:Y→Zとφ:X→Y（HAと一致、model構造やfibrationの仮定なし）。結論：Over.pullback πの右随伴を選び、そのφでの値π∗Xと任意K→Zに関するHomZ(K,π∗X)≃HomY(K×Z Y,X)の自然全単射を得る（原典の普遍性に一致）。

$`X\to Y` を固定し、すべての試験対象 $`K\to Z` に対するこの対応で $`\pi_*X` を特徴付ける。

:::

:::proposition "ha_B_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomProjection_cartesianFibration")
*HA 命題 B.4.5*　flat fibration の依存積の右 Quillen 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1510)）。対応表の状態：一部（stronger-hyp）。

*主張*　平坦な圏論的ファイブレーション $`\pi:Y\to Z` に沿うスライスの右随伴 $`\pi_*` は Joyal モデル構造に関して右 Quillen である。

KB-W2原文・型再照合：仮定：π:Y→ZをcoCartesian fibration、φを自明な積束Y×D→Y、Dを準圏に限定（Leanが強い：coCartesian π・定数のfiber）。結論：πの各逆像からDへの写像を表す相対指数の射影はCartesian fibrationとなる（この定数束模型でのcategorical fibration保存の強い部分）。一般flat categorical π・任意categorical φの右Quillen性と、右随伴で選んだ依存積との全比較は含まれない。

左随伴の引き戻しは単射を保ち、平坦性を使って自明余ファイブレーションも保つ。この結果、$`X\to Y` が圏論的ファイブレーションなら $`\pi_*X\to Z` も圏論的ファイブレーションである。

:::

