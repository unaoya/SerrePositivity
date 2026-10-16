module
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Complete flatness and complete faithful flatness under the original module equivalences -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
variable {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Complete flatness depends only on the original coefficient module up to linear equivalence. -/
lemma isCompletelyFlat_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N)
    (hM : IsCompletelyFlat I M) : IsCompletelyFlat I N := by
  intro L _ _ hL i hi
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R L)) :=
    hM L hL i hi
  exact hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app (ModuleCat.of R L)).symm

/-- The residue tensor module is compared over the same original quotient ring. -/
lemma isCompletelyFaithfullyFlat_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N)
    (hM : IsCompletelyFaithfullyFlat I M) : IsCompletelyFaithfullyFlat I N := by
  letI := hM.2
  let E : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R ⧸ I) (R ⧸ I)) e
  exact ⟨isCompletelyFlat_of_linearEquiv I e hM.1,
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] M) E.symm⟩

end SerrePositivity
