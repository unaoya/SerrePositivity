module

public import SerrePositivity.KTheory.Adams.WeightDefectLift
public import SerrePositivity.KTheory.Adams.PolynomialNaturality
public import SerrePositivity.KTheory.SupportedCoefficients

/-! # The Adams weight polynomial annihilates supported K0 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct Polynomial
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [CommRing E]

lemma coefficient_empty_zero (x : K0WithSupport.Coefficients E
    (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) : x = 0 :=
  K0WithSupport.coefficient_eq_zero_of_empty_support E x

variable [IsRegularLocalRing R] {p : ℕ}

/-- The proof descends in the height bound and quantifies over all closed supports. -/
lemma LocalizationAdamsFamily.weightPolynomial_annihilates (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d + 1)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E Z) :
    (aeval (F.atBase.operation Z) (weightPolynomial E p c d)) x = 0 := by
  refine Nat.decreasingInduction (motive := fun c _ =>
    ∀ Z : TopologicalSpace.Closeds (PrimeSpectrum R), HeightAtLeast Z c →
      ∀ x : K0WithSupport.Coefficients E Z,
        (aeval (F.atBase.operation Z) (weightPolynomial E p c d)) x = 0) ?_ ?_ hc Z hz x
  · intro c hc ih Z hz x
    rw [weightPolynomial_succ E p c d (by omega), map_mul, Module.End.mul_apply]
    simp only [map_sub, aeval_X, aeval_C]
    change (aeval (F.atBase.operation Z) (weightPolynomial E p (c + 1) d))
      (F.atBase.operation Z x - (p : E) ^ c • x) = 0
    obtain ⟨s, _, y, hheight, hy⟩ := F.weightDefect_lift Z c hz x
    rw [← hy, F.atBase.polynomial_enlarge, ih _ hheight y, map_zero]
  · intro Z hz x
    have he := hz.eq_bot_of_dimension_bound hd
    subst Z
    rw [coefficient_empty_zero x, map_zero]

end Adams
end SerrePositivity
