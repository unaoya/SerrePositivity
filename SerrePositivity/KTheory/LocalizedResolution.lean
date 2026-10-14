module
public import SerrePositivity.KTheory.G0Localization
public import SerrePositivity.HomologicalAlgebra.RegularLocalResolution
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import SerrePositivity.PerfectComplex.ClosedSupportRelations
public import Mathlib.Algebra.Module.FinitePresentation

/-! # Bounded finite free resolutions over localizations of regular local rings

Finite lattices proved in S3 provide descent to the original Noetherian ring.
The descended module need not have the same support before localization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Submonoid R) [IsLocalization P A]

include P in
/-- Finite modules over a localization descend to finitely presented source modules. -/
lemma exists_finitePresentation_descent [IsNoetherianRing R]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ M₀ : ModuleCat.{u} R, Module.Finite R M₀ ∧ Module.FinitePresentation R M₀ ∧
      Nonempty (A ⊗[R] M₀ ≃ₗ[A] M) := by
  obtain ⟨L, hL, hloc⟩ := exists_finite_lattice (B := A) P (N := M)
  have : Module.Finite R L := Module.Finite.of_fg hL
  exact ⟨ModuleCat.of R L, inferInstance, Module.finitePresentation_of_finite R L,
    ⟨hloc.tensorEquiv (B := A)⟩⟩

include P in
/-- A localized regular local resolution resolves every finite localization module. -/
lemma localizedRegularResolution [IsRegularLocalRing R]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (IsResolutionOf F M) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) ∧
      (∀ i, Module.Free A (F.X i)) ∧ (∀ i, Module.Finite A (F.X i)) := by
  obtain ⟨M₀, hfinite, _, ⟨e⟩⟩ := exists_finitePresentation_descent P M
  have := hfinite
  obtain ⟨F, ⟨hF⟩, hb, hfree, hfin⟩ := regularResolution R M₀
  have : Module.Flat R A := IsLocalization.flat A P
  let hA := isResolutionOf_baseChange_of_flat R A M₀ hF
  refine ⟨baseChange (algebraMap R A) F,
    ⟨{ hA with homologyZeroIso := hA.homologyZeroIso ≪≫ e.toModuleIso }⟩,
    baseChange_bounded _ _ hb, ?_, ?_⟩
  · intro i
    have := hfree i
    exact free_baseChange _ _
  · intro i
    have := hfin i
    exact finite_baseChange _ _

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
end SerrePositivity
