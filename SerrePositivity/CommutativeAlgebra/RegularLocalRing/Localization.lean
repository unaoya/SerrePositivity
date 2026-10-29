module
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Criterion
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Dimension
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.PerfectComplex.FiniteProjectiveResolutions

/-! # Regularity of prime localizations without a global dimension assumption -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits Abelian
variable {R : Type u} [CommRing R]

/-- Any prime localization of a regular local ring is regular. -/
theorem isRegularLocalRing_atPrime [IsRegularLocalRing R] (p : PrimeSpectrum R)
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.AtPrime B p.asIdeal] :
    IsRegularLocalRing B := by
  have := IsLocalization.AtPrime.isLocalRing B p.asIdeal
  have := IsLocalization.isNoetherianRing p.asIdeal.primeCompl B
    (inferInstance : IsNoetherianRing R)
  have := hasFiniteProjectiveResolutions_localization (A := B) p.asIdeal.primeCompl
  apply isRegularLocalRing_of_maximalIdeal_projectiveDimension
  exact exists_projectiveDimensionLE_of_resolution_contract
    (ModuleCat.of B (IsLocalRing.maximalIdeal B))
end SerrePositivity

namespace SerrePositivity
open CategoryTheory Limits IsLocalRing RingTheory.Sequence
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The standard prime localization is a regular local ring. -/
theorem isRegularLocalRing_localizationAtPrime (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  isRegularLocalRing_atPrime p (Localization.AtPrime p.asIdeal)

end SerrePositivity
