module

public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryAction

/-!
# 空語余作用と指定augmentationの複体射の一致

Berger–Fresse §1.2.1・§2.2.6、M14 L14、報告 §386。
構成に使った同じ零arity成分をtensorLiftの外延性で戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- L14の零作用は指定した係数augmentationとAW余単位のテンソル（BF §2.2.6）。 -/
lemma coaction_nullary (S : SSet.{0}) :
    cochainAction A S 0 =
      (nullaryCoefficientAugmentation A ⊗ₘ AlexanderWhitney.cochainCounit A S) ≫
        (λ_ (𝟙_ (Complex A))).hom := by
  rw [cochainAction_zero_eq_nullaryAction, nullaryAction, tensorHom_def, Category.assoc,
    leftUnitor_naturality]

end SerrePositivity.EInfinity.SimplexCuts
