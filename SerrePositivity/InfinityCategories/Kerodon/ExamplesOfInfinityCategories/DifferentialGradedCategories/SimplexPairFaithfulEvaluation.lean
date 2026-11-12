module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairOperationNaturality

/-!
# 普遍鎖の評価による等式の検出

概要：普遍模型自身の対角単体への評価に明示的な左逆を与える。
方針：二つの単体射の対のテンソルから、第一の前半と第二の後半を選んで元の対へ戻す。
規約：KST Construction A.5 の普遍模型、追加の射影性や可縮性の仮定を置かない。
使われ方：普遍鎖のサイクル性を実作用素の微分の等式で検証する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：普遍模型の二つの基底のテンソルから交差した座標の対を復元する。
方針：自由化とテンソルの同型を通し、二つの対の第一・第二座標を選ぶ。
規約：KST A.5。使われ方：普遍対角単体への評価の左逆。 -/
def simplexPairEvaluationRetraction (N : ℕ) (r : SimplexCategoryᵒᵖ) :
    (simplicialIntegerTensor (linearizedSpace (simplexPairModel.{u} N))
      (linearizedSpace (simplexPairModel N))).obj r ⟶
      (linearizedSpace (simplexPairModel N)).obj r :=
  (integerTensorIso _ _).hom ≫ integerLinearization.map
    (↾fun z ↦ ULift.up (z.1.down.1, z.2.down.2))

/-- 概要：普遍対角単体への評価の後に座標を選ぶと元の鎖へ戻る。
方針：自由基底上で二つの恒等単体の制限を計算する。
規約：KST A.5、全ての次数の非被約鎖で成立。
使われ方：評価の単射性を仮定せずに得る。 -/
lemma simplexPairEvaluation_retraction (N : ℕ) (r : SimplexCategoryᵒᵖ) :
    (simplexPairEvaluation (linearizedSpace (simplexPairModel.{u} N))
      (linearizedSpace (simplexPairModel N))
      (simplexPairUniversalDiagonal N) (simplexPairUniversalDiagonal N)).app r ≫
      simplexPairEvaluationRetraction N r = 𝟙 _ := by
  apply integerLinearization_hom_ext
  intro z
  change simplexPairEvaluationRetraction N r
    (simplexPairEvaluationApp _ _ _ _ r (integerGenerator z)) = integerGenerator z
  rw [simplexPairEvaluationApp_generator]
  change simplexPairEvaluationRetraction N r
    (TensorProduct.tmul ℤ
      (integerLinearization.map ((simplexPairModel N).map z.down.1.op)
        (simplexPairUniversalDiagonal N))
      (integerLinearization.map ((simplexPairModel N).map z.down.2.op)
        (simplexPairUniversalDiagonal N))) = _
  rw [simplexPairUniversalDiagonal, integerLinearization_map_generator,
    integerLinearization_map_generator]
  change integerLinearization.map _ ((integerTensorIso _ _).hom
    (TensorProduct.tmul ℤ (integerGenerator _) (integerGenerator _))) = _
  rw [integerTensorIso_generator, integerLinearization_map_generator]
  congr 1
  apply ULift.ext
  exact Prod.ext (Category.comp_id z.down.1) (Category.comp_id z.down.2)

/-- 概要：普遍模型自身の対角単体への評価は鎖の等式を検出する。
方針：明示的な左逆を両辺へ適用する。
規約：KST A.5、自由鎖の全ての次数で成立。
使われ方：普遍な比較サイクルの零性を実作用素へ移す。 -/
lemma simplexPairOperation_injective (N : ℕ) (r : SimplexCategoryᵒᵖ) :
    Function.Injective (simplexPairOperation (linearizedSpace (simplexPairModel.{u} N))
      (linearizedSpace (simplexPairModel N)) (N := N) r) := by
  intro z w he
  have ht := congrArg (fun k ↦ k (TensorProduct.tmul ℤ
    (simplexPairUniversalDiagonal N) (simplexPairUniversalDiagonal N))) he
  rw [simplexPairOperation_tmul, simplexPairOperation_tmul] at ht
  have hr := congrArg (fun x ↦ simplexPairEvaluationRetraction N r x) ht
  have hz := congrArg (fun k ↦ k z) (simplexPairEvaluation_retraction.{u} N r)
  have hw := congrArg (fun k ↦ k w) (simplexPairEvaluation_retraction.{u} N r)
  exact hz.symm.trans (hr.trans hw)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
