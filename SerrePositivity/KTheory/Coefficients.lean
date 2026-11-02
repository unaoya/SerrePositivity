module

public import SerrePositivity.KTheory.G0.Functoriality
public import SerrePositivity.KTheory.CoefficientExtension
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup

/-! # 係数を拡大した台つき G₀・K₀

## 概要

台つき G₀ と台つき K₀ の係数の拡大（`⊗ E`）と、台の拡大・基底変更などの基本操作を与える。

## 方針

係数の写像は `LinearMap.baseChange` の別名で、名前は Adams が多用するので残す。

## 規約

PerfectComplex の CoefficientEuler・CubicActionClass が import するので軽く保つ。

## 使われ方

KTheory/Adams の三次の作用、PerfectComplex。
-/

@[expose] public noncomputable section

universe u v

section G0CoefficientsPart

namespace SerrePositivity
open scoped TensorProduct
variable (E : Type v) [CommRing E]
variable {R : Type u} [CommRing R] (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace G0WithSupport
abbrev Coefficients := E ⊗[ℤ] G0WithSupport Z

/-- Coefficient extension of the support enlargement map. -/
def coefficientEnlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    Coefficients E Z →ₗ[E] Coefficients E W := g0CoefficientMap E (enlarge h)

@[simp] lemma coefficientEnlarge_tmul {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (a : E) (x : G0WithSupport Z) :
    coefficientEnlarge E h (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] enlarge h x := rfl

lemma coefficientEnlarge_comp {Z W V : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (h' : W ≤ V) :
    (coefficientEnlarge E h').comp (coefficientEnlarge E h) =
      coefficientEnlarge E (h.trans h') := by
  rw [coefficientEnlarge, coefficientEnlarge, g0CoefficientMap_comp, enlarge_comp]
  rfl

end G0WithSupport
end SerrePositivity

end G0CoefficientsPart

section SupportedCoefficientsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E]

variable {R S : Type u} [CommRing R] [CommRing S]
namespace K0WithSupport
abbrev Coefficients (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) := E ⊗[ℤ] K0WithSupport Z

/-- Extending coefficients preserves the zero group at empty support. -/
lemma coefficient_eq_zero_of_empty_support
    (x : Coefficients E (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) : x = 0 := by
  have : Subsingleton (K0WithSupport (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) :=
    ⟨fun x y => (eq_zero_of_empty_support x).trans (eq_zero_of_empty_support y).symm⟩
  exact Subsingleton.elim x 0

/-- Coefficient-linear maps are determined by supported perfect generators. -/
lemma coefficientHom_ext {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {B : Type*} [AddCommGroup B] [Module E B]
    (F G : Coefficients E Z →ₗ[E] B)
    (h : ∀ X : SupportedPerfectHomotopyOn Z,
      F ((1 : E) ⊗ₜ[ℤ] mk Z X) = G ((1 : E) ⊗ₜ[ℤ] mk Z X)) : F = G := by
  let η : K0WithSupport Z →+ Coefficients E Z :=
    (TensorProduct.mk ℤ E (K0WithSupport Z) (1 : E)).toAddMonoidHom
  have he : F.toAddMonoidHom.comp η = G.toAddMonoidHom.comp η := by
    apply hom_ext
    exact h
  exact coefficientLinearMap_ext E F G (fun x => DFunLike.congr_fun he x)

def coefficientEnlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    Coefficients E Z →ₗ[E] Coefficients E W := g0CoefficientMap E (enlarge h)

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
  rw [enlarge_refl, g0CoefficientMap_id]

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
  exact coefficientPairing_naturality E cup cup (enlarge hY) (enlarge hZ)
    (enlarge (inf_le_inf hY hZ)) (cup_enlarge hY hZ) x y

lemma coefficientCup_map (φ : R →+* S)
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V)
    (x : Coefficients E Y) (y : Coefficients E Z) :
    coefficientMap E φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)
        (coefficientCup E x y) =
      coefficientCup E (coefficientMap E φ Y W hY x) (coefficientMap E φ Z V hZ y) := by
  exact coefficientPairing_naturality E cup cup (map φ Y W hY) (map φ Z V hZ)
    (map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)) (cup_map φ hY hZ) x y

end K0WithSupport
end SerrePositivity

end SupportedCoefficientsPart
