module

public import SerrePositivity.Spectra.General.ShiftedHomSuspension
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomModuleNaturality

/-! # Naturality of the explicit shifted Hom formulas -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- The explicit structure formula is natural in the generator and the target spectrum. -/
@[reassoc]
lemma shiftedHomStructureFormula_naturality (n p q : ℕ) {X Y : C}
    (f : X ⟶ Y) {E F : GeneralSymmetricSpectrum C K} (g : E ⟶ F) :
    shiftedHomStructureFormula n p q Y E ≫
        ((pre f).app (level E (n + (p + q))) ≫
          (ihom X).map (levelMap g (n + (p + q)))) =
      (𝟙 (TensorPowers.power K p) ⊗ₘ
        ((pre f).app (level E (n + q)) ≫ (ihom X).map (levelMap g (n + q)))) ≫
          shiftedHomStructureFormula n p q X F := by
  let map : shiftedHom n Y E ⟶ shiftedHom n X F :=
    SymmetricSequence.freeShiftModuleMap (SymmetricSequence.tensorPowerSequence K) n f g
  have h := structureMap_hom map p q
  simp only [shiftedHom_structureMap_eq_formula, map, SymmetricSequence.freeShiftModuleMap_app] at h
  exact h

/-- The explicit suspension formula is natural in the generator and the target spectrum. -/
@[reassoc]
lemma shiftedHomSuspensionFormula_naturality (n q : ℕ) {X Y : C}
    (f : X ⟶ Y) {E F : GeneralSymmetricSpectrum C K} (g : E ⟶ F) :
    shiftedHomSuspensionFormula n q Y E ≫
        ((pre f).app (level E (n + (q + 1))) ≫
          (ihom X).map (levelMap g (n + (q + 1)))) =
      K ◁ ((pre f).app (level E (n + q)) ≫ (ihom X).map (levelMap g (n + q))) ≫
        shiftedHomSuspensionFormula n q X F := by
  let map : shiftedHom n Y E ⟶ shiftedHom n X F :=
    SymmetricSequence.freeShiftModuleMap (SymmetricSequence.tensorPowerSequence K) n f g
  have h := suspensionMap_hom map q
  simp only [shiftedHom_suspensionMap_eq_formula, levelMap, map,
    SymmetricSequence.freeShiftModuleMap_app] at h
  exact h

end SerrePositivity.GeneralSymmetricSpectrum
