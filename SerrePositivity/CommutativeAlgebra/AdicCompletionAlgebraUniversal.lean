module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import Mathlib.RingTheory.AdicCompletion.Algebra
/-! # The standard extension from an adic completion to a complete algebra

Construct the R-linear extension by module completion. Density in the target
proves multiplicativity. No regularity or Noetherian hypothesis is required.
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type*) [CommRing R] (I : Ideal R) (hI : I.FG)
    (A : Type*) [CommRing A] [Algebra R A] [IsAdicComplete I A]

/-- Extend the original coefficient map to a complete R-algebra. -/
def adicCompletionToCompleteAlgebra : AdicCompletion I R →ₐ[R] A := by
  let f : AdicCompletion I R →ₗ[R] A :=
    (AdicCompletion.ofLinearEquiv I A).symm.toLinearMap.comp
      ((AdicCompletion.map I (Algebra.linearMap R A)).restrictScalars R)
  have hf (r : R) : f (algebraMap R (AdicCompletion I R) r) = algebraMap R A r := by
    change (AdicCompletion.ofLinearEquiv I A).symm
      (AdicCompletion.map I (Algebra.linearMap R A) (AdicCompletion.of I R r)) = _
    rw [AdicCompletion.map_of]
    exact (AdicCompletion.ofLinearEquiv I A).symm_apply_apply _
  apply AlgHom.ofLinearMap f
  · simpa using hf 1
  · intro x y
    have he : f.comp (LinearMap.mulRight R y) =
        (LinearMap.mulRight R (f y)).comp f := by
      apply adicCompletion_linearMap_ext_of_of I hI
      apply LinearMap.ext
      intro r
      change f (algebraMap R (AdicCompletion I R) r * y) =
        f (algebraMap R (AdicCompletion I R) r) * f y
      rw [hf, ← Algebra.smul_def, f.map_smul, Algebra.smul_def]
    exact LinearMap.congr_fun he x

/-- The extension preserves the original map from every coefficient. -/
lemma adicCompletionToCompleteAlgebra_of (r : R) :
    adicCompletionToCompleteAlgebra R I hI A (algebraMap R (AdicCompletion I R) r) =
      algebraMap R A r :=
  (adicCompletionToCompleteAlgebra R I hI A).commutes r

include hI in
/-- Algebra maps from the completion to a complete algebra are unique. -/
lemma adicCompletion_algHom_ext (f g : AdicCompletion I R →ₐ[R] A) : f = g := by
  apply AlgHom.toLinearMap_injective
  apply adicCompletion_linearMap_ext_of_of I hI
  apply LinearMap.ext
  intro r
  exact (f.commutes r).trans (g.commutes r).symm

include hI in
/-- The adic completion has the expected algebra universal property. -/
lemma adicCompletion_existsUnique_algHom : ∃! _f : AdicCompletion I R →ₐ[R] A, True :=
  ⟨adicCompletionToCompleteAlgebra R I hI A, trivial,
    fun f _ => adicCompletion_algHom_ext R I hI A f _⟩
end SerrePositivity
