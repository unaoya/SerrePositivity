module

public import SerrePositivity.KTheory.Coefficients
public import SerrePositivity.PerfectComplex.KoszulClasses

/-! # The common contract for supported Adams operations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct
namespace Adams

/-- The algebraic axioms used by the weight argument on one ring.
Regularity and dimension bounds are separate inputs to that argument. -/
structure SupportedAdams (R : Type u) [CommRing R] (E : Type v) [CommRing E] (p : ℕ) where
  two_le : 2 ≤ p
  operation : (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) →
    K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z
  enlarge : ∀ {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (x : K0WithSupport.Coefficients E Z),
    operation W (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (operation Z x)
  cup : ∀ {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z),
    operation (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      K0WithSupport.coefficientCup E (operation Y x) (operation Z y)
  unit : operation ⊤ ((1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R))) =
    (1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R))
  koszul_one : ∀ a : R,
    operation (supportZeroLocus (Ideal.span ({a} : Set R)))
        ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) =
      (p : E) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a)

lemma koszulClass_zero_enlarge {R : Type u} [CommRing R] (x : Fin 0 → R) :
    K0WithSupport.enlarge (le_top : koszulClosedSupport x ≤ ⊤) (koszulClass x) =
      cyclicUnitClass (R := R) := by
  rw [koszulClass, K0WithSupport.enlarge_mk]
  rfl

namespace SupportedAdams
variable {R : Type u} [CommRing R] {E : Type v} [CommRing E] {p : ℕ}

/-- The finite-sequence normalization is a consequence of the one-element
axiom, multiplicativity, enlargement, and preservation of the unit. -/
lemma koszul (A : SupportedAdams R E p) {n : ℕ} (x : Fin n → R) :
    A.operation (koszulClosedSupport x) ((1 : E) ⊗ₜ[ℤ] koszulClass x) =
      (p : E) ^ n • ((1 : E) ⊗ₜ[ℤ] koszulClass x) := by
  induction n with
  | zero =>
    rw [pow_zero, one_smul]
    apply K0WithSupport.coefficientEnlarge_injective_of_eq E le_top
      (koszulClosedSupport_zero x)
    rw [← A.enlarge]
    simp only [K0WithSupport.coefficientEnlarge_tmul, koszulClass_zero_enlarge, A.unit]
  | succ n ih =>
    rw [koszulClass_succ]
    have ht : (1 : E) ⊗ₜ[ℤ]
        K0WithSupport.cup (oneKoszulClass (x (Fin.last n))) (koszulClass (Fin.init x)) =
      K0WithSupport.coefficientCup E
        ((1 : E) ⊗ₜ[ℤ] oneKoszulClass (x (Fin.last n)))
        ((1 : E) ⊗ₜ[ℤ] koszulClass (Fin.init x)) := by
      simp only [K0WithSupport.coefficientCup_tmul, one_mul]
    rw [← K0WithSupport.coefficientEnlarge_tmul, ht, A.enlarge, A.cup,
      A.koszul_one, ih (Fin.init x)]
    simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_succ]

end SupportedAdams

/-- Operations on all models of localizations of a base ring, with explicit
compatibility for ring maps. Model comparisons and iterated localization maps
are included in the last axiom, rather than treated as definitional equalities. -/
structure LocalizationAdamsFamily (R : Type u) [CommRing R]
    (E : Type v) [CommRing E] (p : ℕ) where
  atBase : SupportedAdams R E p
  atLocalization : (P : Submonoid R) → (A : Type u) → [CommRing A] →
    [Algebra R A] → [IsLocalization P A] → SupportedAdams A E p
  base_naturality : ∀ (P : Submonoid R) (A : Type u) [CommRing A]
    [Algebra R A] [IsLocalization P A]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum A))
    (h : supportPullback (algebraMap R A) Z ≤ W) (x : K0WithSupport.Coefficients E Z),
    K0WithSupport.coefficientMap E (algebraMap R A) Z W h (atBase.operation Z x) =
      (atLocalization P A).operation W
        (K0WithSupport.coefficientMap E (algebraMap R A) Z W h x)
  localization_naturality : ∀ (P Q : Submonoid R) (A B : Type u)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalization P A] [IsLocalization Q B]
    (φ : A →+* B) (_hφ : φ.comp (algebraMap R A) = algebraMap R B)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum A))
    (W : TopologicalSpace.Closeds (PrimeSpectrum B))
    (h : supportPullback φ Z ≤ W) (x : K0WithSupport.Coefficients E Z),
    K0WithSupport.coefficientMap E φ Z W h ((atLocalization P A).operation Z x) =
      (atLocalization Q B).operation W (K0WithSupport.coefficientMap E φ Z W h x)

end Adams
end SerrePositivity
