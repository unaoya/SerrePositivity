module

public import SerrePositivity.KTheory.K0Localization
public import SerrePositivity.KTheory.Coefficients
public import SerrePositivity.KTheory.CoefficientExactness
public import Mathlib.RingTheory.Localization.Submodule
public import SerrePositivity.KTheory.G0.MaximalSupport
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # 係数つきの台つき K₀ の局所化と極大台の長さ

## 概要

係数を拡大した台つき K₀ の局所化と、有限な極大台上の G₀ の係数つきの長さの座標を与える。

## 方針

係数なしの局所化（`K0Localization`・`LocalizationCoefficients`）に係数の拡大を合わせる。

## 規約

局所化の完全列の一本化は保留（refactor-plan §6.2.3）。

## 使われ方

KTheory/Adams の係数つきの重みの議論。
-/

@[expose] public noncomputable section

universe u v

section K0LocalizationCoefficientsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable (E : Type v) [CommRing E] {R S : Type u} [CommRing R] [CommRing S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [HasFiniteProjectiveResolutions R] [HasFiniteProjectiveResolutions S]

namespace K0WithSupport
def coefficientHomologyEuler (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    Coefficients E Z →ₗ[E] G0WithSupport.Coefficients E Z := g0CoefficientMap E (homologyEuler Z)

def coefficientResolutionMap (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    G0WithSupport.Coefficients E Z →ₗ[E] Coefficients E Z :=
  g0CoefficientMap E (G0WithSupport.resolutionMap Z)

lemma coefficientResolutionMap_homologyEuler (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (x : Coefficients E Z) : coefficientResolutionMap E Z (coefficientHomologyEuler E Z x) = x := by
  change ((g0CoefficientMap E (G0WithSupport.resolutionMap Z)).comp
    (g0CoefficientMap E (homologyEuler Z))) x = x
  rw [g0CoefficientMap_comp, resolutionMap_homologyEuler, g0CoefficientMap_id]
  rfl

omit [IsNoetherianRing R] in
lemma coefficientResolutionMap_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) :
    (coefficientEnlarge E h).comp (coefficientResolutionMap E Z) =
      (coefficientResolutionMap E W).comp (G0WithSupport.coefficientEnlarge E h) := by
  unfold coefficientEnlarge coefficientResolutionMap G0WithSupport.coefficientEnlarge
  rw [g0CoefficientMap_comp, g0CoefficientMap_comp, G0WithSupport.resolutionMap_enlarge]

variable [Algebra R S] (P : Submonoid R) [IsLocalization P S]

def coefficientLocalize (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    Coefficients E Z →ₗ[E] Coefficients E (supportPullback (algebraMap R S) Z) :=
  g0CoefficientMap E (localize (S := S) P Z)

lemma coefficientHomologyEuler_localize (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    (coefficientHomologyEuler E (supportPullback (algebraMap R S) Z)).comp
      (coefficientLocalize (S := S) E P Z) =
    (G0WithSupport.coefficientLocalize (B := S) E P Z).comp (coefficientHomologyEuler E Z) := by
  unfold coefficientLocalize coefficientHomologyEuler G0WithSupport.coefficientLocalize
  rw [g0CoefficientMap_comp, g0CoefficientMap_comp, homologyEuler_localize]

lemma coefficientLocalize_surjective (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    Function.Surjective (coefficientLocalize (S := S) E P Z) :=
  LinearMap.lTensor_surjective E (localize_surjective (S := S) P Z)

lemma coefficientLocalize_kernel_supported (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (x : Coefficients E Z) (hx : coefficientLocalize (S := S) E P Z x = 0) :
    ∃ s ∈ P, ∃ y : Coefficients E (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      coefficientEnlarge E inf_le_left y = x := by
  have h := DFunLike.congr_fun (coefficientHomologyEuler_localize (S := S) E P Z) x
  change coefficientHomologyEuler E _ (coefficientLocalize E P Z x) =
    G0WithSupport.coefficientLocalize E P Z (coefficientHomologyEuler E Z x) at h
  rw [hx, map_zero] at h
  obtain ⟨s, hs, y, hy⟩ := G0WithSupport.coefficientLocalize_kernel_supported (B := S) E P Z
    (coefficientHomologyEuler E Z x) h.symm
  refine ⟨s, hs, coefficientResolutionMap E _ y, ?_⟩
  have hn := DFunLike.congr_fun (coefficientResolutionMap_enlarge E
    (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z from inf_le_left)) y
  change coefficientEnlarge E inf_le_left (coefficientResolutionMap E _ y) =
    coefficientResolutionMap E Z (G0WithSupport.coefficientEnlarge E inf_le_left y) at hn
  rw [hy] at hn
  exact hn.trans (coefficientResolutionMap_homologyEuler E Z x)

lemma coefficientLocalize_away_kernel_range (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (s : R) [IsLocalization.Away s S] :
    (coefficientLocalize (S := S) E (Submonoid.powers s) Z).ker =
      (coefficientEnlarge E (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)).range :=
  g0CoefficientMap_ker_eq_range E _ _
    (localize_away_kernel_range (S := S) Z s)
    (localize_surjective (S := S) (Submonoid.powers s) Z)

omit [IsNoetherianRing S] [HasFiniteProjectiveResolutions S] in
/-- Target hypotheses are supplied by the proved localization stability results. -/
lemma localize_surjective_of_resolution_contract (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    Function.Surjective (localize (S := S) P Z) := by
  have := IsLocalization.isNoetherianRing P S (inferInstance : IsNoetherianRing R)
  have := hasFiniteProjectiveResolutions_of_localization (S := S) P
  exact localize_surjective P Z

omit [IsNoetherianRing S] [HasFiniteProjectiveResolutions S] in
lemma localize_kernel_supported_of_resolution_contract
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (x : K0WithSupport Z)
    (hx : localize (S := S) P Z x = 0) :
    ∃ s ∈ P, ∃ y : K0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x := by
  have := IsLocalization.isNoetherianRing P S (inferInstance : IsNoetherianRing R)
  have := hasFiniteProjectiveResolutions_of_localization (S := S) P
  exact localize_kernel_supported P Z x hx

omit [IsNoetherianRing S] [HasFiniteProjectiveResolutions S] in
lemma coefficientLocalize_kernel_supported_of_resolution_contract
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (x : Coefficients E Z)
    (hx : coefficientLocalize (S := S) E P Z x = 0) :
    ∃ s ∈ P, ∃ y : Coefficients E (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      coefficientEnlarge E inf_le_left y = x := by
  have := IsLocalization.isNoetherianRing P S (inferInstance : IsNoetherianRing R)
  have := hasFiniteProjectiveResolutions_of_localization (S := S) P
  exact coefficientLocalize_kernel_supported E P Z x hx

end K0WithSupport
end SerrePositivity

end K0LocalizationCoefficientsPart

section MaximalSupportCoefficientLengthPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct IsLocalRing
namespace Adams
variable (E : Type v) [CommRing E] {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)
variable [Fintype {p : PrimeSpectrum R // p ∈ W}]

def coefficientG0LengthEquiv : G0WithSupport.Coefficients E W ≃ₗ[E]
    ({p : PrimeSpectrum R // p ∈ W} → E) := by
  classical
  exact ((maximalLengthEquiv W hw).toIntLinearEquiv.baseChange ℤ E _ _) ≪≫ₗ
    TensorProduct.piScalarRight ℤ E E {p : PrimeSpectrum R // p ∈ W}

lemma coefficientG0LengthEquiv_tmul (a : E) (x : G0WithSupport W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientG0LengthEquiv E W hw (a ⊗ₜ[ℤ] x) p =
      a * (localLengthMap W hw p.val x : E) := by
  classical
  change (TensorProduct.piScalarRightHom ℤ E E _
    (a ⊗ₜ[ℤ] maximalLengthEvaluation W hw x)) p = _
  rw [TensorProduct.piScalarRightHom_tmul]
  simp only [maximalLengthEvaluation_apply, zsmul_eq_mul, mul_comm]

end Adams
end SerrePositivity

end MaximalSupportCoefficientLengthPart
