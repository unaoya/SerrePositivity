module

public import SerrePositivity.Spectra.General.ShiftedHom

/-! # Level comparisons for the internal Hom out of a free spectrum -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- The m-th level of the Hom spectrum out of a free spectrum in degree n. -/
def internalHomFreeAtLevelIso (n m : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    level (internalHom ((freeAt (K := K) n).obj X) E) m ≅ (ihom X).obj (level E (n + m)) :=
  (evaluation m).mapIso (internalHomShiftIso n X E)

/-- 次数をずらした内部Homの構造射は、各段の比較で元の構造射を移した射。 -/
lemma shiftedHom_structureMap (n p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    structureMap (shiftedHom n X E) p q =
      (𝟙 (TensorPowers.power K p) ⊗ₘ (internalHomFreeAtLevelIso n q X E).inv) ≫
        structureMap (internalHom ((freeAt n).obj X) E) p q ≫
          (internalHomFreeAtLevelIso n (p + q) X E).hom := by
  have h := structureMap_hom (internalHomShiftIso n X E).inv p q
  change structureMap (shiftedHom n X E) p q ≫
      (internalHomFreeAtLevelIso n (p + q) X E).inv =
    (𝟙 (TensorPowers.power K p) ⊗ₘ (internalHomFreeAtLevelIso n q X E).inv) ≫
      structureMap (internalHom ((freeAt n).obj X) E) p q at h
  have h' := congrArg (fun k => k ≫ (internalHomFreeAtLevelIso n (p + q) X E).hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

/-- 次数をずらした内部Homの懸垂構造射も各段の比較による移送で計算できる。 -/
lemma shiftedHom_suspensionMap (n q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    suspensionMap (shiftedHom n X E) q =
      K ◁ (internalHomFreeAtLevelIso n q X E).inv ≫
          suspensionMap (internalHom ((freeAt n).obj X) E) q ≫
            (internalHomFreeAtLevelIso n (q + 1) X E).hom := by
  have h := suspensionMap_hom (internalHomShiftIso n X E).inv q
  change suspensionMap (shiftedHom n X E) q ≫
      (internalHomFreeAtLevelIso n (q + 1) X E).inv =
    K ◁ (internalHomFreeAtLevelIso n q X E).inv ≫
      suspensionMap (internalHom ((freeAt n).obj X) E) q at h
  have h' := congrArg (fun k => k ≫ (internalHomFreeAtLevelIso n (q + 1) X E).hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

/-- F_nからの内部Homの構造射も各段の比較と値域の構造射の直接公式で計算できる。 -/
lemma internalHomFreeAt_structureMap_formula (n p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    structureMap (internalHom ((freeAt n).obj X) E) p q =
      (𝟙 (TensorPowers.power K p) ⊗ₘ (internalHomFreeAtLevelIso n q X E).hom) ≫
        shiftedHomStructureFormula n p q X E ≫ (internalHomFreeAtLevelIso n (p + q) X E).inv := by
  apply (cancel_mono (internalHomFreeAtLevelIso n (p + q) X E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← shiftedHom_structureMap_eq_formula]
  exact structureMap_hom (internalHomShiftIso n X E).hom p q

end SerrePositivity.GeneralSymmetricSpectrum
