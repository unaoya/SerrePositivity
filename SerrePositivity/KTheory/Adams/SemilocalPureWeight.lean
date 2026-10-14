module

public import SerrePositivity.KTheory.Adams.IteratedPrimeLocalization
public import SerrePositivity.KTheory.Adams.MaximalPureWeight
public import SerrePositivity.KTheory.Adams.CoefficientLengthEquiv

/-! # Pure Adams weight after least-height semilocalization -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open IsLocalRing
namespace Adams
variable {R B : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing B] [Algebra R B]
variable {E : Type v} [CommRing E] {p : ℕ}
variable (F : LocalizationAdamsFamily R E p)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ)
variable [IsLocalization (heightStratumComplement Z c) B]

/-- On the least-height support in the semilocal ring, the operation is p^c. -/
lemma LocalizationAdamsFamily.semilocal_pureWeight (h : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E (supportPullback (algebraMap R B) Z)) :
    (F.atLocalization (heightStratumComplement Z c) B).operation
        (supportPullback (algebraMap R B) Z) x = (p : E) ^ c • x := by
  let W := supportPullback (algebraMap R B) Z
  let hw : ∀ q ∈ W, q.asIdeal.IsMaximal := fun q hq => (h.mem_pullback_iff_isMaximal q).mp hq
  let := IsLocalization.isNoetherianRing (heightStratumComplement Z c) B
    (inferInstance : IsNoetherianRing R)
  let := hasFiniteProjectiveResolutions_of_localization (S := B) (heightStratumComplement Z c)
  have hf : (W : Set (PrimeSpectrum B)).Finite :=
    h.finite_localized_maximal_points.subset (fun q hq => (h.mem_pullback_iff_isMax q).mp hq)
  let := hf.fintype
  apply sub_eq_zero.mp
  apply coefficient_eq_zero_of_localizations E W hw
  intro q
  let T := Localization.AtPrime q.val.asIdeal
  let r := PrimeSpectrum.comap (algebraMap R B) q.val
  let : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : SMul B T := (inferInstance : Algebra B T).toSMul
  let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime T r.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (heightStratumComplement Z c) T q.val.asIdeal
  have hr : r.asIdeal.height = (c : ℕ∞) :=
    ((h.mem_pullback_iff_heightStratum q.val).mp q.property).2
  obtain ⟨hregular, hd⟩ := iteratedPrime_regular_dimension
    (heightStratumComplement Z c) q.val c hr
  let := hregular
  let ht := maximalSupport_pullback_le W hw q.val
  have hn := F.localization_naturality (heightStratumComplement Z c) r.asIdeal.primeCompl B T
    (algebraMap B T) (IsScalarTower.algebraMap_eq R B T).symm
    W (supportZeroLocus (maximalIdeal T)) ht x
  have hpure := (F.atLocalization r.asIdeal.primeCompl T).maximal_pureWeight c hd
    (K0WithSupport.coefficientMap E (algebraMap B T) W
      (supportZeroLocus (maximalIdeal T)) ht x)
  rw [map_sub, map_smul, hn, hpure, sub_self]

end Adams
end SerrePositivity
