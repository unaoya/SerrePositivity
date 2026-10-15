module

public import SerrePositivity.Spectra.General.ShiftedHom

/-! # The actual bonding map of a shifted internal Hom spectrum

The formula is the closed transpose of evaluation, the original bonding map,
and the explicit output block permutation. It applies to arbitrary C,K.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

def shiftedHomSuspensionIndex (n q : ℕ) :
    FiniteBijection.of ((n + q) + 1) ⟶ FiniteBijection.of (n + (q + 1)) :=
  eqToHom (congrArg FiniteBijection.of (Nat.one_add (n + q)).symm) ≫
    shiftedHomStructureIndex n 1 q ≫
      eqToHom (congrArg FiniteBijection.of (congrArg (n + ·) (Nat.one_add q)))

@[reassoc] lemma shiftedHom_evaluation_index_eq (n : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) {a b : ℕ} (h : a = b) :
    X ◁ eqToHom (congrArg (level (shiftedHom n X E)) h) ≫
        (ihom.ev X).app (level E (n + b)) =
      (ihom.ev X).app (level E (n + a)) ≫
        eqToHom (congrArg (level E) (congrArg (n + ·) h)) := by
  subst b
  simp

omit [HasLimitsOfSize.{0, 0} C] in
lemma suspensionMap_shiftedIndex (n q : ℕ) (E : GeneralSymmetricSpectrum C K) :
    suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q) =
      (TensorPowers.oneIso K).inv ▷ level E (n + q) ≫ structureMap E 1 (n + q) ≫
        E.X.map (shiftedHomStructureIndex n 1 q) ≫
          eqToHom (congrArg (level E) (congrArg (n + ·) (Nat.one_add q))) := by
  unfold suspensionMap shiftedHomSuspensionIndex
  erw [Functor.map_comp, Functor.map_comp]
  erw [eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[reassoc] lemma shiftedHom_suspensionMap_evaluation (n q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    X ◁ suspensionMap (shiftedHom n X E) q ≫
        (ihom.ev X).app (level E (n + (q + 1))) =
      (α_ X K (level (shiftedHom n X E) q)).inv ≫
        (β_ X K).hom ▷ level (shiftedHom n X E) q ≫
          (α_ K X (level (shiftedHom n X E) q)).hom ≫
            K ◁ (ihom.ev X).app (level E (n + q)) ≫
              suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q) := by
  rw [suspensionMap_shiftedIndex]
  unfold suspensionMap
  change X ◁ ((TensorPowers.oneIso K).inv ▷ level (shiftedHom n X E) q ≫
      structureMap (shiftedHom n X E) 1 q ≫
        eqToHom (congrArg (level (shiftedHom n X E)) (Nat.one_add q))) ≫
      (ihom.ev X).app (level E (n + (q + 1))) = _
  simp only [whiskerLeft_comp, Category.assoc]
  rw [shiftedHom_evaluation_index_eq n X E (Nat.one_add q)]
  rw [shiftedHom_structureMap_evaluation_assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right, comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]

def shiftedHomSuspensionFormula (n q : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    K ⊗ (ihom X).obj (level E (n + q)) ⟶ (ihom X).obj (level E (n + (q + 1))) :=
  MonoidalClosed.curry
    ((α_ X K ((ihom X).obj (level E (n + q)))).inv ≫
      (β_ X K).hom ▷ (ihom X).obj (level E (n + q)) ≫
        (α_ K X ((ihom X).obj (level E (n + q)))).hom ≫
          K ◁ (ihom.ev X).app (level E (n + q)) ≫
            suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q))

lemma shiftedHom_suspensionMap_eq_formula (n q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    suspensionMap (shiftedHom n X E) q = shiftedHomSuspensionFormula n q X E := by
  apply MonoidalClosed.uncurry_injective
  unfold shiftedHomSuspensionFormula
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  exact shiftedHom_suspensionMap_evaluation n q X E

end SerrePositivity.GeneralSymmetricSpectrum
