module

public import SerrePositivity.KTheory.Adams.MaximalLengthEquiv
public import SerrePositivity.PerfectComplex.CoefficientEuler
public import SerrePositivity.KTheory.MaximalSupportCoefficientLength
public import SerrePositivity.KTheory.ComparisonNaturality
public import SerrePositivity.KTheory.CoefficientLinearExtension

/-! # Coefficient length coordinates and joint injectivity of supported localizations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct IsLocalRing
namespace Adams
variable (E : Type v) [CommRing E] {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)
variable [Fintype {p : PrimeSpectrum R // p ∈ W}]

variable [HasFiniteProjectiveResolutions R]

def coefficientK0LengthEquiv : K0WithSupport.Coefficients E W ≃ₗ[E]
    ({p : PrimeSpectrum R // p ∈ W} → E) :=
  ((k0G0WithSupportEquiv W).toIntLinearEquiv.baseChange ℤ E _ _) ≪≫ₗ
    coefficientG0LengthEquiv E W hw

lemma coefficientK0LengthEquiv_tmul (a : E) (x : K0WithSupport W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientK0LengthEquiv E W hw (a ⊗ₜ[ℤ] x) p =
      a * (localLengthMap W hw p.val (K0WithSupport.homologyEuler W x) : E) := by
  change coefficientG0LengthEquiv E W hw
    (a ⊗ₜ[ℤ] K0WithSupport.homologyEuler W x) p = _
  exact coefficientG0LengthEquiv_tmul E W hw a _ p

omit [Fintype {p : PrimeSpectrum R // p ∈ W}] in
lemma localLengthMap_homologyEuler (p : PrimeSpectrum R) (x : K0WithSupport W) :
    localLengthMap W hw p (K0WithSupport.homologyEuler W x) =
      K0WithSupport.integerEuler (Localization.AtPrime p.asIdeal)
        (K0WithSupport.map (algebraMap R (Localization.AtPrime p.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.asIdeal)))
          (maximalSupport_pullback_le W hw p) x) := by
  let T := Localization.AtPrime p.asIdeal
  let := hasFiniteProjectiveResolutions_of_localization (S := T) p.asIdeal.primeCompl
  have he := DFunLike.congr_fun (K0WithSupport.homologyEuler_map (algebraMap R T)
    (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat T p.asIdeal.primeCompl)
    W (supportZeroLocus (maximalIdeal T)) (maximalSupport_pullback_le W hw p)) x
  exact congrArg (maximalSupportLengthMap T) he.symm

lemma coefficientK0LengthEquiv_apply_local (x : K0WithSupport.Coefficients E W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientK0LengthEquiv E W hw x p =
      K0WithSupport.coefficientEuler E (Localization.AtPrime p.val.asIdeal)
        (K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
          (maximalSupport_pullback_le W hw p.val) x) := by
  have he : (LinearMap.proj p).comp (coefficientK0LengthEquiv E W hw).toLinearMap =
      (K0WithSupport.coefficientEuler E (Localization.AtPrime p.val.asIdeal)).comp
        (K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
          (maximalSupport_pullback_le W hw p.val)) := by
    apply coefficientLinearMap_ext E
    intro y
    change coefficientK0LengthEquiv E W hw ((1 : E) ⊗ₜ[ℤ] y) p = _
    rw [coefficientK0LengthEquiv_tmul, LinearMap.comp_apply,
      K0WithSupport.coefficientMap_tmul, K0WithSupport.coefficientEuler_tmul,
      localLengthMap_homologyEuler]
  exact DFunLike.congr_fun he x

omit [Fintype {p : PrimeSpectrum R // p ∈ W}] in
/-- Joint localizations detect zero on finite maximal support with any coefficients. -/
lemma coefficient_eq_zero_of_localizations [Finite {p : PrimeSpectrum R // p ∈ W}]
    (x : K0WithSupport.Coefficients E W)
    (hx : ∀ p : {p : PrimeSpectrum R // p ∈ W},
      K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
        (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
        (maximalSupport_pullback_le W hw p.val) x = 0) : x = 0 := by
  letI := Fintype.ofFinite {p : PrimeSpectrum R // p ∈ W}
  apply (coefficientK0LengthEquiv E W hw).injective
  rw [map_zero]
  funext p
  rw [coefficientK0LengthEquiv_apply_local, hx, map_zero]
  rfl

end Adams
end SerrePositivity
