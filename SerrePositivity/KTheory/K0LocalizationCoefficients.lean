module
public import SerrePositivity.KTheory.K0Localization
public import Mathlib.RingTheory.Localization.Submodule

/-! # Supported K₀ localization with extended coefficients -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open scoped TensorProduct
variable (E : Type v) [CommRing E] {R S : Type u} [CommRing R] [CommRing S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [HasFiniteProjectiveResolutions R] [HasFiniteProjectiveResolutions S]

namespace K0WithSupport
abbrev Coefficients (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) := E ⊗[ℤ] K0WithSupport Z

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

def coefficientEnlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    Coefficients E Z →ₗ[E] Coefficients E W := g0CoefficientMap E (enlarge h)

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
        from inf_le_left)).range := by
  have he : Function.Exact
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)).toIntLinearMap
      (localize (S := S) (Submonoid.powers s) Z).toIntLinearMap := by
    intro x
    exact Iff.of_eq (congrArg (fun H : AddSubgroup (K0WithSupport Z) => x ∈ H)
      (localize_away_kernel_range (S := S) Z s))
  exact LinearMap.exact_iff.mp
    (lTensor_exact E he (localize_surjective (S := S) (Submonoid.powers s) Z))

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
