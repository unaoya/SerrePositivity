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

/-- The comparison carries each original submodule inclusion to its subtype map. -/
lemma finiteSubmoduleColimitIso_ι (N : ModuleCat.{u} R)
    (P : {P : Submodule R N // P.FG}) :
    colimit.ι (ModuleCat.directLimitDiagram
      (fun Q : {Q : Submodule R N // Q.FG} => ↥Q.val)
      (fun _ _ h => Submodule.inclusion h)) P ≫
        (finiteSubmoduleColimitIso N).hom = ModuleCat.ofHom P.val.subtype := by
  classical
  simp only [finiteSubmoduleColimitIso]
  ext x
  simp [ModuleCat.directLimitCocone, Submodule.FG.directLimit]
  let G := fun Q : {Q : Submodule R N // Q.FG} => ↥Q.val
  let f := fun (Q Q' : {Q : Submodule R N // Q.FG}) (h : Q ≤ Q') =>
    Submodule.inclusion h
  change (Module.DirectLimit.lift R _ G f (fun Q => Q.val.subtype) (fun _ _ _ _ => rfl))
    (Module.DirectLimit.of R _ G f P x) = P.val.subtype x
  apply Module.DirectLimit.lift_of

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

/-- The full almost-Tor input is equivalent to its finitely generated tests;
the ideal, all positive degrees, and all coefficient scalars are retained. -/
lemma torCoefficientScalarEndomorphism_all_iff_finite
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C) :
    (∀ (N : ModuleCat.{u} R) (i : ℕ), 0 < i →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N i c = 0) ↔
    (∀ (N : ModuleCat.{u} R), Module.Finite R N → ∀ (i : ℕ), 0 < i →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N i c = 0) := by
  constructor
  · intro h N _ i hi c hc
    exact h N i hi c hc
  · intro h N i hi c hc
    exact torCoefficientScalarEndomorphism_eq_zero_of_finite C i c
      (fun M hM => h M hM i hi c hc) N

end SerrePositivity
