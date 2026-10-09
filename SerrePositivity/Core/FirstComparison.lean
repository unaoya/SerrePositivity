module

public import SerrePositivity.Core.Setup
public import SerrePositivity.PerfectComplex.Basic
public import SerrePositivity.IntersectionMultiplicity.TwistEvaluation

/-!
# Assembling Lemma 5.2

The norm comparison from Lemma 3.5, the identifications of its evaluations,
and the independent finite-extension rank comparison give `FirstComparison`.
The inputs are explicit arguments; the resolution, its support, and the Tor
identifications are not assumed to have been constructed yet.

Restriction-of-scalars twisting uses the inverse index in the normalized
evaluation. The final sum is reindexed by inversion.
-/

public section

universe u

open CategoryTheory

namespace SerrePositivity.CoreData

variable {R : Type u} [CommRing R] {P Q : Ideal R} (X : CoreData R P Q)

/-- The final assembly of Lemma 5.2 from the norm comparison and the rank
comparison. Every still-needed mathematical identification is an explicit input. -/
theorem firstComparison_of_complex
    (L : CochainComplex (ModuleCat.{u} X.D') ℤ)
    (hfinite : ∀ (σ : X.GD) (i : ℤ),
      X.lamD.len ((baseChange (algebraMap X.D' X.CD) (twist σ L)).homology i) ≠ ⊤)
    (hnorm : (∑ σ : X.GD, chiOrd (twist σ L)) =
      ∑ σ : X.GD, chiLam X.lamD (algebraMap X.D' X.CD) (twist σ L))
    (hOrd : ∀ σ : X.GD, chiOrd (twist σ L) = (chi R X.D' X.E' : ℝ))
    (hLam : ∀ σ : X.GD,
      chiLam X.lamD (algebraMap X.D' X.CD) (twist σ L) = X.c σ⁻¹)
    (hTor : ∀ (σ : X.GD) (i : ℕ),
      TorAlg (X.iota σ) i X.E' ≃ₗ[X.CD]
        ((baseChange (algebraMap X.D' X.CD) (twist σ⁻¹ L)).homology (-(i : ℤ))))
    (hRanks : chi R X.D' X.E' = (X.aD : ℤ) * X.aE * chi R (R ⧸ P) (R ⧸ Q)) :
    X.FirstComparison := by
  have hfiniteTor : ∀ (σ : X.GD) (i : ℕ), X.lamD.len (TorAlg (X.iota σ) i X.E') ≠ ⊤ := by
    intro σ i
    have hlen := X.lamD.len_congr _ _ (hTor σ i)
    exact ne_of_eq_of_ne hlen (hfinite σ⁻¹ (-(i : ℤ)))
  have hsum : (∑ σ : X.GD, X.c σ⁻¹) = ∑ σ : X.GD, X.c σ :=
    Fintype.sum_equiv (Equiv.inv X.GD) _ _ (fun _ ↦ rfl)
  have hcomparison : (Fintype.card X.GD : ℝ) * (chi R X.D' X.E' : ℝ) =
      ∑ σ : X.GD, X.c σ := by
    simp_rw [hOrd, hLam] at hnorm
    rw [hsum] at hnorm
    simpa using hnorm
  have hRanksReal : (chi R X.D' X.E' : ℝ) =
      (X.aD : ℝ) * X.aE * (chi R (R ⧸ P) (R ⧸ Q) : ℝ) := by
    exact_mod_cast hRanks
  refine ⟨hfiniteTor, ?_⟩
  rw [← hcomparison, hRanksReal]
  ring

/-- Assemble Lemma 5.2 directly from a cochain resolution of `E'`. The Tor
and normalized-Euler identifications, including inverse twisting, are now
derived rather than passed as inputs. Ordinary twisting invariance is automatic.

The remaining inputs are the norm comparison from Lemma 3.5, the ordinary
evaluation of the untwisted complex, and the independent rank comparison. -/
theorem firstComparison_of_resolution
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsResolutionOf F (ModuleCat.of R X.E'))
    (hfinite : ∀ (σ : X.GD) (i : ℤ),
      X.lamD.len ((baseChange (algebraMap X.D' X.CD)
        (twist σ (baseChange (algebraMap R X.D') F))).homology i) ≠ ⊤)
    (hnorm : (∑ σ : X.GD, chiOrd (twist σ (baseChange (algebraMap R X.D') F))) =
      ∑ σ : X.GD, chiLam X.lamD (algebraMap X.D' X.CD)
        (twist σ (baseChange (algebraMap R X.D') F)))
    (hOrd : chiOrd (baseChange (algebraMap R X.D') F) = (chi R X.D' X.E' : ℝ))
    (hRanks : chi R X.D' X.E' = (X.aD : ℤ) * X.aE * chi R (R ⧸ P) (R ⧸ Q)) :
    X.FirstComparison := by
  apply X.firstComparison_of_complex (baseChange (algebraMap R X.D') F) hfinite hnorm
    (fun σ ↦ (chiOrd_twist σ _).trans hOrd) ?_ ?_ hRanks
  · intro σ
    simpa only [c, iota] using
      chiLam_twist_baseChange_resolution X.lamD (algebraMap R X.D')
        (algebraMap X.D' X.CD) σ hF
  · intro σ i
    have key (g : X.GD) : TorAlg (X.iota g⁻¹) i X.E' ≃ₗ[X.CD]
        ((baseChange (algebraMap X.D' X.CD)
          (twist g (baseChange (algebraMap R X.D') F))).homology (-(i : ℤ))) :=
      torAlgTwistBaseChangeEquiv (algebraMap R X.D') (algebraMap X.D' X.CD) g hF i
    have key' (g k : X.GD) (hk : g⁻¹ = k) : TorAlg (X.iota k) i X.E' ≃ₗ[X.CD]
        ((baseChange (algebraMap X.D' X.CD)
          (twist g (baseChange (algebraMap R X.D') F))).homology (-(i : ℤ))) := by
      subst k
      exact key g
    exact key' σ⁻¹ σ (inv_inv σ)

end SerrePositivity.CoreData
