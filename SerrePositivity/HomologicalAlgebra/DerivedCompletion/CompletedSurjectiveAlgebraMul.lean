module
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The original completed multiplication of a surjective algebra -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The original derived multiplication of a surjective algebra is an H⁰ isomorphism. -/
lemma surjectiveAlgebraMul_h0_isIso
    (A : Type u) [CommRing A] [Algebra R A]
    (hs : Function.Surjective (algebraMap R A)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) := by
  have hl : IsIso (ModuleCat.ofHom (LinearMap.mul' R A)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (LinearMap.mul'_bijective_of_surjective R A hs)
  have ha := derivedTensorAugmentation_h0_isIso (ModuleCat.of R A) (ModuleCat.of R A)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- Discreteness of the actual completed self-tensor inverts the original completed product.
The coefficient algebra is complete and the original structure map is surjective. -/
lemma completedSurjectiveAlgebraMul_isIso (a : R)
    (A : Type u) [CommRing A] [Algebra R A]
    (hs : Function.Surjective (algebraMap R A))
    (hc : IsModuleComplete R a (ModuleCat.of R A))
    (hpure :
      let X := (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))
      X.obj.IsGE 0 ∧ X.obj.IsLE 0) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) := by
  let X := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)
  let F := derivedComplexCompletionFunctor R a
  let f : X.obj ⟶ Y.obj := (boundedAboveDerivedAlgebraMul (R := R) A).hom
  letI : Y.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)).IsLE 0
    infer_instance
  letI : Y.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)).IsGE 0
    infer_instance
  have hX : X.obj.IsLE 0 := by
    change (boundedAboveDerivedTensor.obj (Y, Y)).obj.IsLE 0
    infer_instance
  have hY : Y.obj.IsLE 0 := inferInstance
  have h0 := derivedComplexCompletion_h0_map_isIso R a f hX hY
    (surjectiveAlgebraMul_h0_isIso R A hs)
  letI : (F.obj X.obj).IsGE 0 := hpure.1
  letI : (F.obj X.obj).IsLE 0 := hpure.2
  let eY : Y.obj ≅ F.obj Y.obj := derivedComplexCompletionUnitIso R a Y.obj hc
  letI : (F.obj Y.obj).IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eY 0
  letI : (F.obj Y.obj).IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eY 0
  apply (DerivedCategory.isIso_iff (ModuleCat R) (F.map f)).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    exact h0
  · have hzX : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (F.obj X.obj)) := by
      by_cases hpos : 0 < i
      · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
      · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
    have hzY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (F.obj Y.obj)) := by
      by_cases hpos : 0 < i
      · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
      · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
    exact hzX.isIso hzY _

end SerrePositivity.DerivedCompletion
