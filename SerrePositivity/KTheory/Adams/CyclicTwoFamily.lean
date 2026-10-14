module

public import SerrePositivity.KTheory.Adams.Family
public import SerrePositivity.KTheory.Adams.BaseChangeNaturality

/-! # The cyclic Adams square supplies the common localization-family contract -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E] {R S : Type u} [CommRing R] [CommRing S]
namespace Adams
variable [Invertible (2 : R)]

def coefficientCyclicTwo (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z :=
  g0CoefficientMap E (cyclicTwo Z)

@[simp]
lemma coefficientCyclicTwo_tmul (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (a : E) (x : K0WithSupport Z) :
    coefficientCyclicTwo E Z (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] cyclicTwo Z x := rfl

lemma coefficientCyclicTwo_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (x : K0WithSupport.Coefficients E Z) :
    coefficientCyclicTwo E W (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (coefficientCyclicTwo E Z x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [coefficientCyclicTwo_tmul, K0WithSupport.coefficientEnlarge_tmul]
    exact congrArg (fun z => a ⊗ₜ[ℤ] z) (cyclicTwo_enlarge h x)
  | add x y hx hy => simp only [map_add, hx, hy]

lemma coefficientCyclicTwo_cup {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z) :
    coefficientCyclicTwo E (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      K0WithSupport.coefficientCup E (coefficientCyclicTwo E Y x) (coefficientCyclicTwo E Z y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [coefficientCyclicTwo_tmul, K0WithSupport.coefficientCup_tmul]
      exact congrArg (fun z => (a * b) ⊗ₜ[ℤ] z) (cyclicTwo_cup x y)
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

lemma coefficientCyclicTwo_map [Invertible (2 : S)] (φ : R →+* S)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientMap E φ Z W h (coefficientCyclicTwo E Z x) =
      coefficientCyclicTwo E W (K0WithSupport.coefficientMap E φ Z W h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [coefficientCyclicTwo_tmul, K0WithSupport.coefficientMap_tmul]
    exact congrArg (fun z => a ⊗ₜ[ℤ] z) (cyclicTwo_map φ Z W h x)
  | add x y hx hy => simp only [map_add, hx, hy]

def supportedCyclicTwo : SupportedAdams R E 2 where
  two_le := le_refl 2
  operation := coefficientCyclicTwo E
  enlarge := coefficientCyclicTwo_enlarge E
  cup := coefficientCyclicTwo_cup E
  unit := by rw [coefficientCyclicTwo_tmul, cyclicTwo_unit]
  koszul_one a := by
    rw [coefficientCyclicTwo_tmul, cyclicTwo_oneKoszul]
    simp only [Nat.cast_ofNat, two_smul, tmul_add]

lemma coefficientCyclicTwo_koszul {n : ℕ} (x : Fin n → R) :
    coefficientCyclicTwo E (koszulClosedSupport x) ((1 : E) ⊗ₜ[ℤ] koszulClass x) =
      (2 : E) ^ n • ((1 : E) ⊗ₜ[ℤ] koszulClass x) :=
  (supportedCyclicTwo E).koszul x

omit [CommRing S] in
/-- A source inverse for 2 supplies one in every algebra over the source. -/
@[instance_reducible]
def algebraInvertibleTwo (A : Type u) [CommRing A] [Algebra R A] : Invertible (2 : A) := by
  simpa only [map_ofNat] using Invertible.map (algebraMap R A) (2 : R)

/-- All localizations, their maps, and their model comparisons satisfy the contract. -/
def cyclicTwoFamily : LocalizationAdamsFamily R E 2 where
  atBase := supportedCyclicTwo E
  atLocalization _ A := by
    intro _ _ _
    let := algebraInvertibleTwo (R := R) A
    exact supportedCyclicTwo E
  base_naturality := by
    intro P A _ _ _ Z W h x
    let := algebraInvertibleTwo (R := R) A
    exact coefficientCyclicTwo_map E (algebraMap R A) Z W h x
  localization_naturality := by
    intro P Q A B _ _ _ _ _ _ φ _ Z W h x
    let := algebraInvertibleTwo (R := R) A
    let := algebraInvertibleTwo (R := R) B
    exact coefficientCyclicTwo_map E φ Z W h x

end Adams
end SerrePositivity
