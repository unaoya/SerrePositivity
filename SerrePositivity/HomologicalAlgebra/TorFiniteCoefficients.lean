module

public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Higher Tor annihilation can be tested on finitely generated coefficients

Use the actual filtered diagram of finitely generated submodules, retaining the
original Tor scalar maps. No completeness or Noetherian assumption is required.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- The original module is the categorical colimit of its finitely generated
submodules, via the standard module direct limit. -/
def finiteSubmoduleColimitIso (N : ModuleCat.{u} R) :
    colimit (ModuleCat.directLimitDiagram
      (fun P : {P : Submodule R N // P.FG} => ↥P.val)
      (fun _ _ h => Submodule.inclusion h)) ≅ N := by
  classical
  exact colimit.isoColimitCocone
    ⟨_, ModuleCat.directLimitIsColimit _ _⟩ ≪≫
      (Submodule.FG.directLimit R N).toModuleIso

/-- A colimit-preserving functor detects a zero natural map on its stages. -/
lemma natTrans_colimit_app_eq_zero
    {J : Type u} [Category J] (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (τ : F ⟶ G) (D : J ⥤ ModuleCat.{u} R) [HasColimit D]
    [PreservesColimit D F] (h : ∀ j, τ.app (D.obj j) = 0) :
    τ.app (colimit D) = 0 := by
  apply (isColimitOfPreserves F (colimit.isColimit D)).hom_ext
  intro j
  change F.map (colimit.ι D j) ≫ τ.app (colimit D) =
    F.map (colimit.ι D j) ≫ 0
  rw [τ.naturality, h, zero_comp, comp_zero]

/-- A coefficient scalar kills Tor for every module if it kills Tor for every
finitely generated module. The Tor degree and scalar are unchanged. -/
lemma torCoefficientScalarEndomorphism_eq_zero_of_finite
    (C : Type u) [CommRing C] [Algebra R C] (i : ℕ) (c : C)
    (h : ∀ (N : ModuleCat.{u} R), Module.Finite R N →
      torCoefficientScalarEndomorphism C N i c = 0)
    (N : ModuleCat.{u} R) : torCoefficientScalarEndomorphism C N i c = 0 := by
  classical
  let J := {P : Submodule R N // P.FG}
  let : Nonempty J := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun P Q =>
    ⟨⟨P.val ⊔ Q.val, P.property.sup Q.property⟩, le_sup_left, le_sup_right⟩⟩
  let : AB5OfSize.{0, u} (ModuleCat.{u} R) :=
    AB5OfSize_of_univLE.{0, u, u, u} _
  let D := ModuleCat.directLimitDiagram (fun P : J => ↥P.val)
    (fun _ _ h => Submodule.inclusion h)
  let F := (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)
  let τ := (Tor (ModuleCat.{u} R) i).map
    (ModuleCat.ofHom (LinearMap.mulLeft R c))
  let := tor_preservesExactColimits (J := J) (ModuleCat.of R C) i
  have hz : τ.app (colimit D) = 0 := by
    apply natTrans_colimit_app_eq_zero F F τ D
    intro P
    exact h _ (Module.Finite.iff_fg.mpr P.property)
  let e := finiteSubmoduleColimitIso N
  change τ.app N = 0
  rw [← cancel_epi (F.map e.hom), τ.naturality, hz, zero_comp, comp_zero]

end SerrePositivity
