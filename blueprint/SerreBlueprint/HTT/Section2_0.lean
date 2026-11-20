-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.BoundaryFactorization
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodyneFactorization
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightAnodyneFactorization
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 2.0 Fibrations of Simplicial Sets（章の導入）" =>
%%%
number := false
tag := "htt-2-0"
%%%

HTT 2.0 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "htt_2_0_0_1" (lean := "SSet.modelCategoryQuillen.fibration_iff, SSet.anodyneExtensions")
*HTT 例 2.0.0.1*　Kan ファイブレーションとアノダイン射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=71)）。対応表の状態：Mathlib にある。

*主張*　すべての角包含に右持ち上げ性を持つ射を Kan ファイブレーションといい、それらすべてに左持ち上げ性を持つ射をアノダイン射という。

仮定：単体集合の射（HTT と一致）。結論：ファイブレーションは全ホーンに対する右持ち上げ、アノダイン射はその左直交類（一致）。

Kan ファイブレーションの角埋めでは、空間の中の角だけでなく、その底における延長も指定する。アノダイン射は同じ持ち上げ問題を左側の射の性質として読む。

:::

:::proposition "htt_2_0_0_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.boundaryInclusions_rlp_eq, SSet.modelCategoryQuillen.cofibration_iff")
*HTT 例 2.0.0.2*　自明ファイブレーションと余ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=71)）。対応表の状態：本体にある。

*主張*　全境界包含に右持ち上げ性を持つ射が自明ファイブレーションであり、それらすべてに左持ち上げ性を持つ射はちょうど単体的集合の単射である。

仮定：任意の単体集合の射（HTT と一致）。結論：境界包含に対する右持ち上げは自明 Kan ファイブレーションに等しく、余ファイブレーションは単射である（一致）。

境界を指定して単体を一つ付ける操作が、単体的部分集合を大きくする基本操作になる。これが角に対する右持ち上げより強い条件を使う理由である。

:::

:::definition "htt_2_0_0_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration, SSet.InnerFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions, SSet.innerAnodyneExtensions")
*HTT 定義 2.0.0.3*　左右・内ファイブレーションの定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=71)）。対応表の状態：本体にある。

*主張*　左・右・内ファイブレーションは、それぞれ $`0\le i<n`、$`0<i\le n`、$`0<i<n` の角包含に対する右持ち上げ性で定まり、対応する左持ち上げ類を左・右・内アノダインと呼ぶ。

仮定：単体集合の射（HTT と一致）。結論：指定したホーンの右直交類を左右・内ファイブレーションとし、その各左直交類を対応するアノダイン射とする（一致）。

左と右は内角に加えて異なる片側の外角を含む。「左アノダイン」の左は、左ファイブレーションに対する左持ち上げという対応とともに読む。

:::

:::proposition "htt_2_0_0_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_innerFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_innerFibration")
*HTT 注意 2.0.0.5*　ファイブレーションの含意関係（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=72)）。対応表の状態：一部（component）。

*主張*　自明ファイブレーションから Kan、左・右、余 Cartesian・Cartesian、圏論的、内ファイブレーションへ進む含意があり、一般には逆向きの含意はない。

KB-W2原文・型再照合：仮定：単体集合の射（HTT と一致）。結論：自明・Kan・左または右・内ファイブレーション間の含意の一部（Lean が弱い：(co)Cartesian と圏論的ファイブレーションまで含む図および逆向きの反例を揃えていない）。

左ファイブレーションは余 Cartesian 側、右ファイブレーションは Cartesian 側の特別な場合である。両側の経路は圏論的ファイブレーションで合流する。

:::

:::proposition "htt_2_0_0_6" (lean := "SerrePositivity.SimplicialModel.AnodyneKanReplacement.factorization, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_leftAnodyne_leftFibration_factorization, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.exists_mono_trivialKan_factorization")
*HTT 注意 2.0.0.6*　五つの持ち上げ条件の因子分解（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=72)）。対応表の状態：本体にある。

*主張*　任意の単体的写像は、小対象論法により、アノダインと Kan、左・右・内アノダインと対応するファイブレーション、または単射と自明ファイブレーションの組へ因子分解できる。

仮定：任意の単体集合間の射（HTT と一致）。結論：全ホーン・左・右・内のアノダインと対応ファイブレーション、および単射と自明 Kan ファイブレーションの分解を得る（一致）。

右因子に欲しい持ち上げ性に合わせて、左因子を作る際の付け足しに用いる生成包含を選ぶ。境界を生成元にすれば単射と自明ファイブレーション、片側の角を使えば左・右の組になる。

:::

:::proposition "htt_2_0_0_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftFibration_op_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_op_leftFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalRightAnodyne_op_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftAnodyne_op_of_rightAnodyne, SSet.opFunctorCompOpFunctorIso")
*HTT 注意 2.0.0.7*　反対単体集合による左右の双対（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=73)）。対応表の状態：本体にある。

*主張*　反対化は左ファイブレーションと右ファイブレーションを交換し、左アノダインと右アノダインも交換する。

仮定：任意の単体集合の射（HTT と一致）。結論：ファイブレーションとアノダイン射のそれぞれで、反転が左条件と右条件を交換し、二重反転の同型で逆向きも得る（一致）。

頂点順序の反転は添字 $`i` の角を添字 $`n-i` の角へ送る。従って初端と終端のどちらを含めるかが入れ替わり、持ち上げ方の双対性が得られる。

:::

