module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear

/-! # The actual completion and completed tensor on zero coefficient modules -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The original completion of a zero derived object is zero. -/
lemma derivedCompletion_isZero_of_isZero (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsZero X) : IsZero ((derivedComplexCompletionFunctor R a).obj X) := by
  have hc : IsComplete R a X := isComplete_of_scalar_pow_zero R a X 1 (hX.eq_of_src _ _)
  exact hX.of_iso (derivedComplexCompletionUnitIso R a X hc).symm

/-- The actual bounded single object of a zero module is zero. -/
lemma boundedAboveDerivedSingle_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    IsZero (boundedAboveDerivedSingleFunctor.obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply InducedCategory.hom_ext
  exact ((DerivedCategory.singleFunctor (ModuleCat R) 0).map_isZero hM).eq_of_src _ _

/-- A zero left coefficient gives a zero original completed tensor. -/
lemma completedTensor_isZero_of_left_isZero (a : R) (M N : ModuleCat.{u} R)
    (hM : IsZero M) :
    IsZero (((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)))).obj := by
  have hz := (tensorRight (boundedAboveDerivedSingleFunctor.obj N)).map_isZero
    (boundedAboveDerivedSingle_isZero R M hM)
  have hz' := DerivedCategory.Minus.ι.map_isZero hz
  exact derivedCompletion_isZero_of_isZero R a _ hz'

/-- A zero right coefficient gives a zero original completed tensor as well. -/
lemma completedTensor_isZero_of_right_isZero (a : R) (M N : ModuleCat.{u} R)
    (hN : IsZero N) :
    IsZero (((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)))).obj := by
  have hz := (tensorLeft (boundedAboveDerivedSingleFunctor.obj M)).map_isZero
    (boundedAboveDerivedSingle_isZero R N hN)
  have hz' := DerivedCategory.Minus.ι.map_isZero hz
  exact derivedCompletion_isZero_of_isZero R a _ hz'

end SerrePositivity.DerivedCompletion
