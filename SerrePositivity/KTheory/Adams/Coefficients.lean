module

public import SerrePositivity.KTheory.K0LocalizationCoefficients
public import SerrePositivity.PerfectComplex.TensorBaseChange
public import SerrePositivity.PerfectComplex.IntegerEuler

/-! # Cup products and Euler evaluation with extended coefficients -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E]

/-- Regard a biadditive pairing as a bilinear map over the integers. -/
def integerPairing {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) : A →ₗ[ℤ] B →ₗ[ℤ] C where
  toFun x := (f x).toIntLinearMap
  map_add' x y := by ext z; exact congrArg (fun g : B →+ C => g z) (f.map_add x y)
  map_smul' n x := by ext z; exact congrArg (fun g : B →+ C => g z) (f.map_zsmul n x)

/-- Extend both arguments of an integer pairing to an E-bilinear pairing. -/
def coefficientPairing {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) : E ⊗[ℤ] A →ₗ[E] E ⊗[ℤ] B →ₗ[E] E ⊗[ℤ] C :=
  TensorProduct.curry
    ((TensorProduct.lift (integerPairing f)).baseChange E ∘ₗ
      (AlgebraTensorModule.distribBaseChange ℤ E A B).symm.toLinearMap)

@[simp]
lemma coefficientPairing_tmul {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) (a b : E) (x : A) (y : B) :
    coefficientPairing E f (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = (a * b) ⊗ₜ[ℤ] f x y := by
  simp only [coefficientPairing, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]
  rfl

variable {R S : Type u} [CommRing R] [CommRing S]
namespace K0WithSupport
variable {Y Z Y' Z' : TopologicalSpace.Closeds (PrimeSpectrum R)}

def coefficientCup : Coefficients E Y →ₗ[E] Coefficients E Z →ₗ[E] Coefficients E (Y ⊓ Z) :=
  coefficientPairing E cup

@[simp]
lemma coefficientCup_tmul (a b : E) (x : K0WithSupport Y) (y : K0WithSupport Z) :
    coefficientCup E (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = (a * b) ⊗ₜ[ℤ] cup x y :=
  coefficientPairing_tmul E cup a b x y

/-- Coefficient extension of the existing closed-support ring-change map. -/
def coefficientMap (φ : R →+* S) (Y : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Y ≤ W) :
    Coefficients E Y →ₗ[E] Coefficients E W := g0CoefficientMap E (map φ Y W h)

@[simp]
lemma coefficientMap_tmul (φ : R →+* S) (Y : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Y ≤ W)
    (a : E) (x : K0WithSupport Y) :
    coefficientMap E φ Y W h (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] map φ Y W h x := rfl

@[simp]
lemma coefficientEnlarge_tmul (h : Y ≤ Y') (a : E) (x : K0WithSupport Y) :
    coefficientEnlarge E h (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] enlarge h x := rfl

lemma coefficientEnlarge_comp {V : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Y ≤ Z) (h' : Z ≤ V) :
    (coefficientEnlarge E h').comp (coefficientEnlarge E h) =
      coefficientEnlarge E (h.trans h') := by
  unfold coefficientEnlarge
  rw [g0CoefficientMap_comp, enlarge_comp]

lemma coefficientEnlarge_refl : coefficientEnlarge E (le_refl Y) = LinearMap.id := by
  unfold coefficientEnlarge
  rw [enlarge_refl]
  ext a
  rfl

lemma coefficientEnlarge_injective_of_eq (h : Y ≤ Y') (he : Y = Y') :
    Function.Injective (coefficientEnlarge E h) := by
  subst Y'
  change Function.Injective (coefficientEnlarge E (le_refl Y))
  rw [coefficientEnlarge_refl]
  exact fun _ _ h => h

lemma coefficientMap_comp {T : Type u} [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    (Y : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S))
    (V : TopologicalSpace.Closeds (PrimeSpectrum T))
    (hφ : supportPullback φ Y ≤ W) (hψ : supportPullback ψ W ≤ V)
    (hcomp : supportPullback (ψ.comp φ) Y ≤ V) :
    (coefficientMap E ψ W V hψ).comp (coefficientMap E φ Y W hφ) =
      coefficientMap E (ψ.comp φ) Y V hcomp := by
  unfold coefficientMap
  rw [g0CoefficientMap_comp, map_comp]

lemma coefficientCup_enlarge (hY : Y ≤ Y') (hZ : Z ≤ Z')
    (x : Coefficients E Y) (y : Coefficients E Z) :
    coefficientEnlarge E (inf_le_inf hY hZ) (coefficientCup E x y) =
      coefficientCup E (coefficientEnlarge E hY x) (coefficientEnlarge E hZ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [coefficientCup_tmul, coefficientEnlarge_tmul]
      exact congrArg (fun z => (a * b) ⊗ₜ[ℤ] z) (cup_enlarge hY hZ x y)
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

lemma coefficientCup_map (φ : R →+* S)
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V)
    (x : Coefficients E Y) (y : Coefficients E Z) :
    coefficientMap E φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)
        (coefficientCup E x y) =
      coefficientCup E (coefficientMap E φ Y W hY x) (coefficientMap E φ Z V hZ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [coefficientCup_tmul, coefficientMap_tmul]
      exact congrArg (fun z => (a * b) ⊗ₜ[ℤ] z) (cup_map φ hY hZ x y)
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

variable (R) [IsNoetherianRing R] [IsLocalRing R]

/-- The integer Euler map followed by extension of coefficients and E ⊗ ℤ ≃ E. -/
def coefficientEuler : Coefficients E (supportZeroLocus (IsLocalRing.maximalIdeal R)) →ₗ[E] E :=
  (AlgebraTensorModule.rid ℤ E E).toLinearMap ∘ₗ g0CoefficientMap E (integerEuler R)

@[simp]
lemma coefficientEuler_tmul (a : E)
    (x : K0WithSupport (supportZeroLocus (IsLocalRing.maximalIdeal R))) :
    coefficientEuler E R (a ⊗ₜ[ℤ] x) = a * (integerEuler R x : E) := by
  simp only [coefficientEuler, LinearMap.comp_apply, g0CoefficientMap_tmul,
    LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul, zsmul_eq_mul, mul_comm]

end K0WithSupport
end SerrePositivity
