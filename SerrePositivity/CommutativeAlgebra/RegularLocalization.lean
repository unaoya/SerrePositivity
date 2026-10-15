module
public import SerrePositivity.CommutativeAlgebra.RegularLocalCriterion
public import SerrePositivity.CommutativeAlgebra.RegularPrimeDimension
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

/-- A prime localization has a Koszul resolution of its residue field of length ht(p). -/
lemma exists_localized_height_koszulResolution (p : PrimeSpectrum R) :
    ∃ z : Fin p.asIdeal.height.toNat → Localization.AtPrime p.asIdeal,
      Ideal.span (Set.range z) = maximalIdeal (Localization.AtPrime p.asIdeal) ∧
      IsWeaklyRegular (Localization.AtPrime p.asIdeal) (List.ofFn z) ∧
      Nonempty (IsResolutionOf (koszulComplex z)
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          ((Localization.AtPrime p.asIdeal) ⧸ maximalIdeal (Localization.AtPrime p.asIdeal)))) := by
  let B := Localization.AtPrime p.asIdeal
  have : IsRegularLocalRing B := isRegularLocalRing_localizationAtPrime p
  obtain ⟨rs, hrs, hgen, hdim⟩ := exists_regular_generators B
  have hlen : rs.length = p.asIdeal.height.toNat := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B,
      ← natCast_primeHeight_toNat p] at hdim
    exact_mod_cast hdim.symm
  rw [← hlen]
  have hspan : Ideal.span (Set.range rs.get) = Ideal.ofList rs := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_iff_get.symm
  have hz : Ideal.span (Set.range rs.get) = maximalIdeal B := hspan.trans hgen
  have hreg : IsWeaklyRegular B (List.ofFn rs.get) := by simpa using hrs
  refine ⟨rs.get, hz, hreg, ?_⟩
  rw [← hz]
  exact ⟨isResolutionOf_koszul rs.get (isKoszulResolution_of_isWeaklyRegular rs.get hreg)⟩
end SerrePositivity
