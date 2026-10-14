module

public import SerrePositivity.CommutativeAlgebra.RegularLocalization
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Comparing a prime localization of a localization with a base prime localization -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
namespace Adams
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Comparison as an R-algebra, retaining the composed structure map. -/
def iteratedPrimeLocalizationEquiv (P : Submonoid R) [IsLocalization P B]
    (q : PrimeSpectrum B) :
    letI : Algebra R (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp (algebraMap R B)).toAlgebra
    Localization.AtPrime (PrimeSpectrum.comap (algebraMap R B) q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal := by
  let T := Localization.AtPrime q.asIdeal
  letI : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  letI : SMul R T := (inferInstance : Algebra R T).toSMul
  letI : SMul B T := (inferInstance : Algebra B T).toSMul
  letI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.AtPrime T (PrimeSpectrum.comap (algebraMap R B) q).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization P T q.asIdeal
  exact IsLocalization.algEquiv
    (PrimeSpectrum.comap (algebraMap R B) q).asIdeal.primeCompl
    (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R B) q).asIdeal) T

/-- A prime localization of any localization of a regular local ring is regular;
its dimension is the height of its contracted prime. -/
lemma iteratedPrime_regular_dimension [IsRegularLocalRing R]
    (P : Submonoid R) [IsLocalization P B] (q : PrimeSpectrum B) (c : ℕ)
    (hc : (PrimeSpectrum.comap (algebraMap R B) q).asIdeal.height = (c : ℕ∞)) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) ∧
      ringKrullDim (Localization.AtPrime q.asIdeal) = c := by
  let T := Localization.AtPrime q.asIdeal
  let : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : SMul B T := (inferInstance : Algebra B T).toSMul
  let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime T (PrimeSpectrum.comap (algebraMap R B) q).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization P T q.asIdeal
  refine ⟨isRegularLocalRing_atPrime (PrimeSpectrum.comap (algebraMap R B) q) T, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (PrimeSpectrum.comap (algebraMap R B) q).asIdeal T, hc]
  rfl

end Adams
end SerrePositivity
