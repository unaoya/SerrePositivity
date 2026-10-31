module
public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory

/-! # Finite projective resolutions independently of Grothendieck groups -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Submonoid R) [IsLocalization P A]

/-- The finite-projective contract used by the abstract K₀/G₀ comparison. -/
class HasFiniteProjectiveResolutions (A : Type u) [CommRing A] : Prop where
  exists_resolution (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (IsResolutionOf F M) ∧ strictlyPerfectComplex A F

/-- Convert the existing bounded finite free contract into a strictly perfect complex. -/
lemma strictlyPerfectComplex_of_bounded_free
    (F : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i))
    (hfree : ∀ i, Module.Free A (F.X i)) (hfinite : ∀ i, Module.Finite A (F.X i)) :
    strictlyPerfectComplex A F := by
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨⟨a, b, ?_, ?_⟩, fun i => ?_⟩
  · exact (F.isStrictlyGE_iff a).mpr (fun i hi => hab i (Or.inl hi))
  · exact (F.isStrictlyLE_iff b).mpr (fun i hi => hab i (Or.inr hi))
  · have := hfree i
    exact ⟨hfinite i, Module.Projective.of_free⟩

include P in
/-- The resolution contract for a localization, obtained without its local regularity. -/
lemma hasFiniteProjectiveResolutions_localization [IsRegularLocalRing R] :
    HasFiniteProjectiveResolutions A where
  exists_resolution M h := by
    have := h
    obtain ⟨F, hF, hb, hf, hfin⟩ := localizedRegularResolution P M
    exact ⟨F, hF, strictlyPerfectComplex_of_bounded_free F hb hf hfin⟩

instance hasFiniteProjectiveResolutions_regular [IsRegularLocalRing A] :
    HasFiniteProjectiveResolutions A where
  exists_resolution M h := by
    have := h
    obtain ⟨F, hF, hb, hf, hfin⟩ := regularResolution A M
    exact ⟨F, hF, strictlyPerfectComplex_of_bounded_free F hb hf hfin⟩

/-- The finite-projective-resolution contract implies finite projective dimension. -/
lemma exists_projectiveDimensionLE_of_resolution_contract [HasFiniteProjectiveResolutions R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : ∃ n, HasProjectiveDimensionLE M n := by
  obtain ⟨F, ⟨hF⟩, hp⟩ := HasFiniteProjectiveResolutions.exists_resolution M
  obtain ⟨a, b, ha, hb⟩ := hp.1
  apply exists_projectiveDimensionLE_of_boundedResolution hF
  exact ⟨a, b, fun i hi => hi.elim
    (fun h => F.isZero_of_isStrictlyGE a i h) (fun h => F.isZero_of_isStrictlyLE b i h)⟩

end SerrePositivity
