module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.CommutativeAlgebra.Koszul

/-!
# Normalized-length part of Lemma 3.5a

The hypotheses of Lemma 3.5a (`A` Noetherian local, `z` a system of parameters,
`T` finite over `A`, `λ H_j(z^v; C) < ∞`) are taken directly as arguments.
The general part (torsion of the homology, descent of `chiLam` to `K₀` once the
evaluations are finite) is in `PerfectComplex/NormalizedEuler.lean`; what remains
here is the Koszul finiteness argument `lemma_3_5a_lam_finite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- The remaining Koszul finiteness argument: use a positive common exponent
from the null homotopies, show finite evaluations for the Koszul tensor complex
by a finite filtration, and extract the original homology as a retract. -/
theorem lemma_3_5a_lam_finite
    (_hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (_hfin : ∀ (v j : ℕ),
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ) :
    lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤ := by
  sorry

/-- **Lemma 3.5a, normalized length**: the independent normalized-length
assertion. Only the Koszul finiteness step remains unproved. -/
theorem lemma_3_5a_lam
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfin : ∀ (v j : ℕ),
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤) :
    (∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) ∧
      (∃ χ : K0Supported T (algebraMap A T ∘ z) →+ ℝ,
        ∀ P, χ (K0.mk P) = chiLam lam (algebraMap T C) P.1) := by
  have hfinite := lemma_3_5a_lam_finite (T := T) hz hfin
  exact ⟨hfinite, chiLamHom_of_finite hz hfinite, chiLamHom_of_finite_mk hz hfinite⟩

end SerrePositivity
