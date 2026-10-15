module
public import SerrePositivity.HomologicalAlgebra.FiniteLocalizationDescent
public import SerrePositivity.HomologicalAlgebra.FiniteFreeBaseChange
public import SerrePositivity.HomologicalAlgebra.RegularLocalResolution
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import Mathlib.RingTheory.Flat.Localization

/-! # Bounded finite free resolutions over localizations of regular local rings -/
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

end SerrePositivity
