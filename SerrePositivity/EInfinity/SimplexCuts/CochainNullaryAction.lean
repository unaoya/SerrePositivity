module

public import SerrePositivity.EInfinity.SimplexCuts.CochainAction

/-!
# 零arityの実際の余作用と元の余単位

Berger–Fresse §2.2.6、M14 L12a、報告 §337。
全整数のtensorLiftの同じ斉次成分で、元のnullaryActionへの複体射の等式を読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 零arityの作用は指定した同じ空語augmentationとAW余単位（BF §2.2.6）。 -/
lemma cochainAction_zero_eq_nullaryAction (A : Type u) [CommRing A] (S : SSet.{0}) :
    cochainAction A S 0 = nullaryAction A S := by
  apply HomologicalComplex.hom_ext
  intro t
  apply mapBifunctor.hom_ext
  intro i j h
  rw [ι_cochainAction]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  rfl

end SerrePositivity.EInfinity.SimplexCuts
