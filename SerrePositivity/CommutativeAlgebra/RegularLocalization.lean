module
public import SerrePositivity.CommutativeAlgebra.RegularLocalCriterion
public import SerrePositivity.CommutativeAlgebra.RegularPrimeDimension
public import SerrePositivity.KTheory.LocalizedResolution
public import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-! # Regularity of prime localizations without a global dimension assumption -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits Abelian
variable {R : Type u} [CommRing R]

/-- A bounded projective resolution supplies the categorical finite-projective-dimension bound. -/
lemma exists_projectiveDimensionLE_of_boundedResolution {M : ModuleCat.{u} R}
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F M)
    (hb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) :
    ∃ n, HasProjectiveDimensionLE M n := by
  obtain ⟨a, b, hb⟩ := hb
  let n := (-a).toNat
  let P := hF.toProjectiveResolution
  refine ⟨n, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y e
  have hz : IsZero (P.complex.X i) := by
    have ht : IsZero (F.X (embUp.f i)) := hb _ (Or.inl (by
      simp only [embUp, ComplexShape.embeddingUpIntLE_f]
      dsimp [n] at hi
      omega))
    exact ht.of_iso (F.restrictionXIso embUp rfl).symm
  obtain ⟨f, hf, he⟩ := P.extMk_surjective e (i + 1) rfl
  have hf0 : f = 0 := hz.eq_zero_of_src f
  rw [← he]
  simp only [hf0, ProjectiveResolution.extMk_zero]

/-- The finite-projective-resolution contract implies finite projective dimension. -/
lemma exists_projectiveDimensionLE_of_resolution_contract [HasFiniteProjectiveResolutions R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : ∃ n, HasProjectiveDimensionLE M n := by
  obtain ⟨F, ⟨hF⟩, hp⟩ := HasFiniteProjectiveResolutions.exists_resolution M
  obtain ⟨a, b, ha, hb⟩ := hp.1
  apply exists_projectiveDimensionLE_of_boundedResolution hF
  exact ⟨a, b, fun i hi => hi.elim
    (fun h => F.isZero_of_isStrictlyGE a i h) (fun h => F.isZero_of_isStrictlyLE b i h)⟩

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
