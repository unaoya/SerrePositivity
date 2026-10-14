module

public import SerrePositivity.KTheory.Adams.WeightDecomposition

/-! # Products add Adams weights, and distinct weights cannot coexist -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] {p : ℕ}
namespace SupportedAdams

lemma cup_eigen (A : SupportedAdams R E p)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) :
    A.operation (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      (p : E) ^ (i + j) • K0WithSupport.coefficientCup E x y := by
  rw [A.cup, hx, hy]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_add, mul_comm]

lemma eigen_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (i : ℕ)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = (p : E) ^ i • x) :
    A.operation W (K0WithSupport.coefficientEnlarge E h x) =
      (p : E) ^ i • K0WithSupport.coefficientEnlarge E h x := by
  rw [A.enlarge, hx, map_smul]

lemma cup_enlarge_eigen (A : SupportedAdams R E p)
    {Y Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Y ⊓ Z ≤ W) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) :
    A.operation W (K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y)) =
      (p : E) ^ (i + j) •
        K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) :=
  A.eigen_enlarge h (i + j) _ (A.cup_eigen i j x y hx hy)

lemma eigen_eq_zero_of_ne (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (a b : E)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = a • x)
    (hy : A.operation Z x = b • x) (hne : a ≠ b) : x = 0 := by
  have hz : (a - b) • x = 0 := by rw [sub_smul, ← hx, ← hy, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

variable [CharZero E]

lemma eigen_eq_zero_of_weight_ne (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = (p : E) ^ i • x)
    (hy : A.operation Z x = (p : E) ^ j • x) (hne : i ≠ j) : x = 0 :=
  A.eigen_eq_zero_of_ne Z _ _ x hx hy
    (fun he => hne (natPow_injective (E := E) A.two_le he))

end SupportedAdams
end Adams
end SerrePositivity
