module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TermwiseComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionTransport
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.RegularLocalResolution
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Derived completeness of tensoring with finite coefficients

Compute the original derived tensor with a finite free resolution of the right
module. The left coefficient module is unresolved and is only assumed derived
complete, with no flatness or regularity assumption.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Tensoring a complete module with a finite free module preserves completeness,
including rank zero and the zero ring. -/
lemma isModuleComplete_tensor_finite_free (M P : ModuleCat.{u} R)
    [Module.Free R P] [Module.Finite R P] (hM : IsModuleComplete R a M) :
    IsModuleComplete R a ((tensorLeft M).obj P) := by
  classical
  let b := (Module.Free.chooseBasis R P).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R P))
  let e := TensorProduct.congr (LinearEquiv.refl R M) b.equivFun ≪≫ₗ
    TensorProduct.piScalarRight R R M _
  apply isModuleComplete_of_linearEquiv R a
    (ModuleCat.of R (Fin (Fintype.card (Module.Free.ChooseBasisIndex R P)) → M))
    (ModuleCat.of R (TensorProduct R M P)) e.symm
  exact isModuleComplete_pi R a (fun _ => M) (fun _ => hM)

/-- Reindexing a chain complex to the standard nonpositive cochain degrees
preserves termwise completeness. The added positive-degree terms are zero. -/
lemma isComplete_Q_extend_chain_of_terms
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ n, IsModuleComplete R a (K.X n)) :
    IsComplete R a (DerivedCategory.Q.obj (K.extend embUp)) := by
  apply isComplete_Q_of_terms R a
  intro i
  by_cases hi : ∃ n, embUp.f n = i
  · obtain ⟨n, rfl⟩ := hi
    exact isModuleComplete_of_linearEquiv R a _ _
      (K.extendXIso embUp rfl).symm.toLinearEquiv (hK n)
  · have hz := HomologicalComplex.isZero_extend_X K embUp i (fun n hn => hi ⟨n, hn⟩)
    let : Subsingleton ((K.extend embUp).X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact isModuleComplete_of_pow_smul_zero R a _ 0 (fun _ => Subsingleton.elim _ _)

/-- Any specified resolution with finite free terms makes the original realized
derived tensor complete. The resolution may have infinite length. -/
lemma realizedDerivedTensor_isComplete_of_finite_free_resolution
    (M N : ModuleCat.{u} R) (P : ProjectiveResolution N)
    (hfree : ∀ n, Module.Free R (P.complex.X n))
    (hfinite : ∀ n, Module.Finite R (P.complex.X n))
    (hM : IsModuleComplete R a M) :
    IsComplete R a ((realizedDerivedTensorFunctor R M).obj N) := by
  apply isComplete_of_iso R a (realizedDerivedTensorResolutionIso M P).symm
  apply isComplete_Q_extend_chain_of_terms R a
  intro n
  let := hfree n
  let := hfinite n
  exact isModuleComplete_tensor_finite_free R a M (P.complex.X n) hM

/-- On a regular local base every finitely generated right coefficient has a
finite free resolution, so the actual two-sided derived tensor is complete. -/
lemma boundedAboveDerivedTensor_isComplete_of_finite_regular [IsRegularLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R N] (hM : IsModuleComplete R a M) :
    IsComplete R a ((boundedAboveDerivedTensorModuleFunctor M).obj N) := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators R
  obtain ⟨P, _, hfree, hfinite⟩ :=
    exists_finite_free_resolution_of_regular_generators rs hreg hgen N
  exact isComplete_of_iso R a (boundedAboveDerivedTensorModuleIso M N).symm
    (realizedDerivedTensor_isComplete_of_finite_free_resolution R a M N P hfree hfinite hM)

end SerrePositivity.DerivedCompletion
