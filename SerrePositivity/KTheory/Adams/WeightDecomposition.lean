module

public import SerrePositivity.KTheory.Adams.WeightAnnihilation
public import SerrePositivity.KTheory.Adams.WeightOperators

/-! # Finite Adams weight decomposition without a finite-dimensional hypothesis -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] [CharZero E] {p : ℕ}

variable [IsRegularLocalRing R]

omit [CharZero E] in
lemma LocalizationAdamsFamily.weightProjector_eigen (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (j : ℕ) (hj : j ∈ Finset.Icc c d) (x : K0WithSupport.Coefficients E Z) :
    F.atBase.operation Z (F.atBase.weightProjector Z c d j x) =
      (p : E) ^ j • F.atBase.weightProjector Z c d j x :=
  lagrangeProjector_eigen _ _ _ j hj x
    (F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

lemma LocalizationAdamsFamily.weightProjector_idem (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (j : ℕ) (hj : j ∈ Finset.Icc c d) :
    F.atBase.weightProjector Z c d j * F.atBase.weightProjector Z c d j =
      F.atBase.weightProjector Z c d j :=
  lagrangeProjector_idem _ _ _ (natPow_injective (E := E) F.atBase.two_le).injOn j hj
    (fun x => F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

omit [CharZero E] in
lemma LocalizationAdamsFamily.weightProjector_orthogonal (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (i j : ℕ) (hj : j ∈ Finset.Icc c d) (hne : i ≠ j) :
    F.atBase.weightProjector Z c d i * F.atBase.weightProjector Z c d j = 0 :=
  lagrangeProjector_orthogonal _ _ _ i j hj hne
    (fun x => F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

/-- Every class has a finite weight decomposition; an empty interval forces the class to zero. -/
lemma LocalizationAdamsFamily.weightDecomposition (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E Z) :
    (∑ j ∈ Finset.Icc c d, F.atBase.weightProjector Z c d j x) = x ∧
      ∀ j ∈ Finset.Icc c d, F.atBase.operation Z (F.atBase.weightProjector Z c d j x) =
        (p : E) ^ j • F.atBase.weightProjector Z c d j x := by
  constructor
  · by_cases hc : c ≤ d
    · exact F.atBase.sum_weightProjector Z c d hc x
    · have hheight : HeightAtLeast Z (d + 1) := by
        intro q hq
        exact (Nat.cast_le.mpr (show d + 1 ≤ c by omega)).trans (hz q hq)
      have he := hheight.eq_bot_of_dimension_bound hd
      subst Z
      rw [coefficient_empty_zero x]
      simp only [map_zero, Finset.sum_const_zero]
  · intro j hj
    have hc : c ≤ d := (Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hj).2
    exact F.weightProjector_eigen d hd c hc Z hz j hj x

end Adams
end SerrePositivity
