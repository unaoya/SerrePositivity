module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # The universal perfectoidization of a perfectoid ring itself -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- The identity on an already perfectoid ring is its universal perfectoidization. -/
theorem IsIntegralPerfectoid.isPerfectoidization_id
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    IsPerfectoidization p (RingHom.id R) := by
  refine ⟨hR, ?_⟩
  intro T _ _ k
  refine ⟨k, RingHom.comp_id k, ?_⟩
  intro l hl
  simpa only [RingHom.comp_id] using hl

end SerrePositivity
