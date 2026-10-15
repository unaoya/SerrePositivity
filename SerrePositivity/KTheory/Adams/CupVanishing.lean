module

public import SerrePositivity.KTheory.Adams.WeightProduct

/-! # Supported cup-product vanishing from the sum of height bounds -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open IsLocalRing
namespace Adams
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {E : Type v} [Field E] [CharZero E] {p : ℕ}

/-- A product of eigenclasses vanishes when its weight differs from the dimension. -/
lemma SupportedAdams.cup_enlarge_eq_zero_of_eigen (A : SupportedAdams R E p)
    (d : ℕ) (hd : ringKrullDim R = d)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Y ⊓ Z ≤ supportZeroLocus (maximalIdeal R)) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) (hne : i + j ≠ d) :
    K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) = 0 :=
  A.eigen_eq_zero_of_weight_ne _ (i + j) d _
    (A.cup_enlarge_eigen h i j x y hx hy) (A.maximal_pureWeight d hd _) hne

/-- High-weight products vanish after enlargement to maximal-ideal support. -/
lemma LocalizationAdamsFamily.cup_enlarge_eq_zero (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R = d)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (cY cZ : ℕ)
    (hY : HeightAtLeast Y cY) (hZ : HeightAtLeast Z cZ) (hc : d < cY + cZ)
    (h : Y ⊓ Z ≤ supportZeroLocus (maximalIdeal R))
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) = 0 := by
  have hx := F.weightDecomposition d hd.le cY Y hY x
  have hy := F.weightDecomposition d hd.le cZ Z hZ y
  have hterm : ∀ i ∈ Finset.Icc cY d, ∀ j ∈ Finset.Icc cZ d,
      K0WithSupport.coefficientEnlarge E h
        (K0WithSupport.coefficientCup E (F.atBase.weightProjector Y cY d i x)
          (F.atBase.weightProjector Z cZ d j y)) = 0 := by
    intro i hi j hj
    apply F.atBase.cup_enlarge_eq_zero_of_eigen d hd h i j _ _ (hx.2 i hi) (hy.2 j hj)
    have hi' := (Finset.mem_Icc.mp hi).1
    have hj' := (Finset.mem_Icc.mp hj).1
    omega
  rw [← hx.1, ← hy.1]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  exact hterm i hi j hj

end Adams
end SerrePositivity
