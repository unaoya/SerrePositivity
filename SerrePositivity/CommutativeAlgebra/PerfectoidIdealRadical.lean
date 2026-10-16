module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPowers
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius

/-! # Radical support and arbitrary positive powers of perfectoid ideals

General perfectoid reducedness supplies the reducedness of the chosen quotient.
The statements retain its original universal map and allow arbitrary p-torsion.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- The actual kernel defining the perfectoid ideal is radical for every g. -/
theorem perfectoidIdeal_isRadical (g : R) :
    (perfectoidIdeal R p hR g).IsRadical := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let T := QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  have hT : IsIntegralPerfectoid T p :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1
  let := hT.isReduced T p
  intro x hx
  obtain ⟨n, hn⟩ := hx
  change κ x = 0
  apply IsReduced.eq_zero
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact hn

/-- Every root of the original principal ideal lies in its perfectoid ideal. -/
theorem radical_span_le_perfectoidIdeal (g : R) :
    (Ideal.span {g}).radical ≤ perfectoidIdeal R p hR g :=
  (perfectoidIdeal_isRadical R p hR g).radical_le_iff.mpr
    (span_le_perfectoidIdeal R p hR g)

/-- Positive powers of any element define the same perfectoid ideal.
No regularity of g or of p is required. -/
theorem perfectoidIdeal_pow_eq (g : R) (n : ℕ) (hn : 0 < n) :
    perfectoidIdeal R p hR (g ^ n) = perfectoidIdeal R p hR g := by
  apply le_antisymm
  · apply perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply perfectoidIdeal_le_of_mem
    apply perfectoidIdeal_isRadical R p hR (g ^ n)
    exact ⟨n, (span_le_perfectoidIdeal R p hR (g ^ n))
      (Ideal.subset_span (Set.mem_singleton _))⟩

end SerrePositivity
