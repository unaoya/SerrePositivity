module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 古典的完備性の線形同値による移送 -/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 線形同値は古典的 I 進完備性を保つ。 -/
theorem isAdicComplete_of_linearEquiv (e : M ≃ₗ[R] N) (hM : IsAdicComplete I M) :
    IsAdicComplete I N := by
  let := hM
  apply AdicCompletion.of_bijective_iff.mp
  have he : (AdicCompletion.of I N : N → AdicCompletion I N) =
      (AdicCompletion.congr I e) ∘ (AdicCompletion.of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr, AdicCompletion.map_of]
  rw [he]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

end SerrePositivity
