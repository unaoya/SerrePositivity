module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionHomologyDivisibility
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorOneCompleteExtension
public import SerrePositivity.CommutativeAlgebra.ConormalIdempotentImage
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps

/-! # Complete almost extension closure from the original completed quotient product

The hypothesis is about the existing standard multiplication on the actual derived
self-tensor of R/I. An H⁰ comparison alone does not supply this hypothesis.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- Inverting the actual derived product after completion makes the original first
quotient self-Tor a-divisible. No vanishing of higher ordinary Tor is assumed. -/
lemma quotientTorOne_smul_surjective_of_completed_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x) := by
  have hH : Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj
        ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R (R ⧸ I))) => a • x) := by
    apply boundedAbove_homology_smul_surjective_of_completion_map_isIso R a
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)) hμ (-1)
    change IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R (R ⧸ I))))
    exact (DerivedCategory.isGE_iff _ 0).mp (inferInstance) (-1) (by omega)
  let e := ((boundedAboveDerivedTensorModuleTorNatIso (ModuleCat.of R (R ⧸ I)) 1).app
    (ModuleCat.of R (R ⧸ I))).toLinearEquiv
  intro x
  obtain ⟨y, hy⟩ := hH (e.symm x)
  refine ⟨e y, ?_⟩
  change a • e y = x
  change a • y = e.symm x at hy
  rw [← e.map_smul, hy, e.apply_symm_apply]

/-- The completed standard quotient product supplies extension closure inside
actual derived-complete modules. -/
lemma completeIdealExtensionClosed_of_completed_quotient_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_quotientTorOne_surjective a I
    (quotientTorOne_smul_surjective_of_completed_mul_isIso a I hμ)

/-- The same completed standard product supplies all ordinary power-quotient
idempotence conditions, using the original ideal and quotient map. -/
lemma ideal_mod_power_idempotent_of_completed_quotient_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) :=
  ideal_mod_power_idempotent_of_conormal_surjective a I
    ((quotientTorOne_smul_surjective_iff_conormal R I a).mp
      (quotientTorOne_smul_surjective_of_completed_mul_isIso a I hμ)) n

end SerrePositivity.DerivedCompletion
