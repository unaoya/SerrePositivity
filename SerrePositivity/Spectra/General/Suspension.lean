module

public import SerrePositivity.Spectra.General.StructureMaps

/-! # Suspension and adjoint bonding maps for an arbitrary coordinate K -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] {K : C}

def suspensionMap (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    K ⊗ level E n ⟶ level E (n + 1) :=
  (TensorPowers.oneIso K).inv ▷ level E n ≫ structureMap E 1 n ≫
    eqToHom (congrArg (level E) (Nat.one_add n))

@[reassoc] lemma suspensionMap_hom {E F : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (n : ℕ) :
    suspensionMap E n ≫ levelMap f (n + 1) =
      K ◁ levelMap f n ≫ suspensionMap F n := by
  have hc := hom_index_eq f (Nat.one_add n)
  simp only [suspensionMap, levelMap, Category.assoc]
  rw [hc]
  rw [← Category.assoc _ _ (eqToHom (congrArg (level F) (Nat.one_add n))), structureMap_hom]
  simp only [id_tensorHom, Category.assoc]
  rw [← Category.assoc, ← whisker_exchange]
  simp only [Category.assoc]
  rfl

def adjointStructureMap (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    level E n ⟶ (ihom K).obj (level E (n + 1)) := curry (suspensionMap E n)

@[reassoc] lemma adjointStructureMap_naturality {E F : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (n : ℕ) :
    levelMap f n ≫ adjointStructureMap F n =
      adjointStructureMap E n ≫ (ihom K).map (levelMap f (n + 1)) := by
  have h := congrArg (fun g ↦ curry g) (suspensionMap_hom f n)
  rw [curry_natural_right, curry_natural_left] at h
  exact h.symm

end SerrePositivity.GeneralSymmetricSpectrum
