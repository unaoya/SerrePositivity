module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairFaithfulEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleChainMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWChainMap

/-!
# AW の後の shuffle の普遍鎖表示

概要：二つの実比較写像の合成を普遍単体模型の具体的な鎖で表す。
方針：AW の切断と shuffle の格子路を後合成し、同じ有限和を自由鎖で取る。
規約：KST Construction A.5 の標準比較、非被約な零次を保持する。
使われ方：恒等との比較ホモトピーの再帰の普遍な差。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：AW→shuffle の合成を表す普遍な N 鎖。
方針：各切断・各格子路で二つの単体射の対を作り、shuffle の符号で足す。
規約：KST A.5、全ての切断は零次も含む。
使われ方：恒等との差の普遍鎖を定める。 -/
def ezUniversalComposite (N : ℕ) :
    (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋N⦌) :=
  ∑ i : Fin (N + 1), ∑ s : ShuffleIndex (i : ℕ) N,
    (-1 : ℤ) ^ s.inversions • integerGenerator (ULift.up
      (s.left ≫ awFront N i, s.right (awDegrees N i) ≫ awBack N i))

/-- 概要：普遍合成鎖の作用素は実 AW の後の実 shuffle に一致。
方針：全テンソルの標準包含で shuffle を評価し、二重有限和を比較する。
規約：KST Construction A.5、任意の単体的整数加群で成立。
使われ方：普遍な差のサイクル性を実鎖写像の微分可換性へ帰着する。 -/
lemma simplexPairOperation_ezComposite (C D : SimplicialObject (ModuleCat.{u} ℤ)) (N : ℕ) :
    simplexPairOperation C D (op ⦋N⦌) (ezUniversalComposite N) =
      alexanderWhitneyApp C D N ≫ shuffleApp C D N := by
  rw [ezUniversalComposite, alexanderWhitneyApp, Preadditive.sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [alexanderWhitneySummand, Category.assoc, ι_shuffleApp, shuffleBidegree,
    Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, simplexPairOperation_generator, Preadditive.comp_zsmul,
    ← integerTensorMap_comp]
  congr 1
  simp only [op_comp, C.map_comp, D.map_comp]

/-- 概要：恒等と AW→shuffle の合成の普遍な差。
方針：普遍対角単体から合成の普遍鎖を引く。
規約：KST A.5、増大の補正と両立する非被約な差。
使われ方：再帰的な標準ホモトピーの各次数の入力。 -/
def ezUniversalDifference (N : ℕ) :
    (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋N⦌) :=
  simplexPairUniversalDiagonal N - ezUniversalComposite N

/-- 概要：普遍な差は恒等と AW→shuffle の合成の実作用素の差に評価される。
方針：作用素の整数線形性と二つの普遍鎖の評価公式を使う。
規約：KST A.5。使われ方：比較ホモトピーの境界の実写像への同定。 -/
lemma simplexPairOperation_ezDifference (C D : SimplicialObject (ModuleCat.{u} ℤ)) (N : ℕ) :
    simplexPairOperation C D (op ⦋N⦌) (ezUniversalDifference N) =
      𝟙 _ - alexanderWhitneyApp C D N ≫ shuffleApp C D N := by
  rw [ezUniversalDifference, map_sub, simplexPairOperation_universalDiagonal,
    simplexPairOperation_ezComposite]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
