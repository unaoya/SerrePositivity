module

public import SerrePositivity.Spectra.General.ShiftedHomNaturality
public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionMiddleExchangeUnit

/-! # Level and structure maps for free spectra in degree zero -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- 生成次数零の懸垂では、次数の移送の他に置換は入らない。 -/
lemma shiftedHomSuspensionIndex_zero (q : ℕ) :
    shiftedHomSuspensionIndex 0 q =
      eqToHom (congrArg FiniteBijection.of
        ((congrArg (· + 1) (Nat.zero_add q)).trans (Nat.zero_add (q + 1)).symm)) := by
  unfold shiftedHomSuspensionIndex
  unfold shiftedHomStructureIndex
  rw [SymmetricSequence.middleExchangeIndex_zero]
  simp only [eqToHom_trans]

/-- 生成次数零の第q段は、そのまま第q段への通常の内部Hom。 -/
def unshiftedHomLevelIso (q : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    level (shiftedHom 0 X E) q ≅ (ihom X).obj (level E q) :=
  eqToIso (congrArg (fun k => (ihom X).obj (level E k)) (Nat.zero_add q))

/-- 添字の置換を使わず値域の構造射から作る通常の内部Homの構造射。 -/
def unshiftedHomStructureFormula (p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    TensorPowers.power K p ⊗ (ihom X).obj (level E q) ⟶ (ihom X).obj (level E (p + q)) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (TensorPowers.power K p) ((ihom X).obj (level E q))).inv ≫
      (β_ X (TensorPowers.power K p)).hom ▷ (ihom X).obj (level E q) ≫
        (α_ (TensorPowers.power K p) X ((ihom X).obj (level E q))).hom ≫
          TensorPowers.power K p ◁ (ihom.ev X).app (level E q) ≫ structureMap E p q)

/-- 通常の内部Homの構造射の直接公式は次数の等式による移送と両立する。 -/
lemma unshiftedHomStructureFormula_index_eq (p : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) {a b : ℕ} (h : a = b) :
    unshiftedHomStructureFormula p a X E ≫
        (ihom X).map (eqToHom (congrArg (level E) (congrArg (p + ·) h))) =
      (𝟙 (TensorPowers.power K p) ⊗ₘ
        ((ihom X).map (eqToHom (congrArg (level E) h)))) ≫
          unshiftedHomStructureFormula p b X E := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, id_tensorHom_id,
    Category.id_comp, Category.comp_id]

/-- 構造射の生成次数零への特殊化を、添字の移送の後合成で表示する。 -/
lemma shiftedHomStructureFormula_zero_raw (p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    shiftedHomStructureFormula 0 p q X E =
      unshiftedHomStructureFormula p (0 + q) X E ≫
        (ihom X).map (E.X.map (shiftedHomStructureIndex 0 p q)) := by
  unfold shiftedHomStructureFormula unshiftedHomStructureFormula
  rw [← CategoryTheory.MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

/-- 生成次数零の構造射の直接公式は通常の内部Homの構造射に移る。 -/
lemma shiftedHomStructureFormula_zero (p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    shiftedHomStructureFormula 0 p q X E ≫ (unshiftedHomLevelIso (p + q) X E).hom =
      (𝟙 (TensorPowers.power K p) ⊗ₘ (unshiftedHomLevelIso q X E).hom) ≫
        unshiftedHomStructureFormula p q X E := by
  rw [shiftedHomStructureFormula_zero_raw]
  simp only [unshiftedHomLevelIso, eqToIso.hom]
  erw [← eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add (p + q))),
    ← eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add q))]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    show shiftedHomStructureIndex 0 p q = _ from SymmetricSequence.middleExchangeIndex_zero p q]
  erw [eqToHom_map]
  rw [eqToHom_trans]
  exact unshiftedHomStructureFormula_index_eq p X E (Nat.zero_add q)

/-- 円による通常の内部Homの懸垂も、値域の懸垂と評価から直接作る。 -/
def unshiftedHomSuspensionFormula (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    K ⊗ (ihom X).obj (level E q) ⟶
      (ihom X).obj (level E (q + 1)) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X K ((ihom X).obj (level E q))).inv ≫
      (β_ X K).hom ▷ (ihom X).obj (level E q) ≫
        (α_ K X ((ihom X).obj (level E q))).hom ≫
          K ◁ (ihom.ev X).app (level E q) ≫ suspensionMap E q)

/-- 通常の内部Homの懸垂の直接公式も次数の等式による移送と両立する。 -/
lemma unshiftedHomSuspensionFormula_index_eq (X : C)
    (E : GeneralSymmetricSpectrum C K) {a b : ℕ} (h : a = b) :
    unshiftedHomSuspensionFormula a X E ≫
        (ihom X).map (eqToHom (congrArg (level E) (congrArg (· + 1) h))) =
      K ◁ ((ihom X).map (eqToHom (congrArg (level E) h))) ≫
          unshiftedHomSuspensionFormula b X E := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id,
    whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- 懸垂の生成次数零への特殊化を、添字の移送の後合成で表示する。 -/
lemma shiftedHomSuspensionFormula_zero_raw (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    shiftedHomSuspensionFormula 0 q X E =
      unshiftedHomSuspensionFormula (0 + q) X E ≫
        (ihom X).map (E.X.map (shiftedHomSuspensionIndex 0 q)) := by
  unfold shiftedHomSuspensionFormula unshiftedHomSuspensionFormula
  rw [← CategoryTheory.MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

/-- 生成次数零の懸垂の直接公式は通常の内部Homの懸垂に移る。 -/
lemma shiftedHomSuspensionFormula_zero (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    shiftedHomSuspensionFormula 0 q X E ≫ (unshiftedHomLevelIso (q + 1) X E).hom =
      K ◁ (unshiftedHomLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  rw [shiftedHomSuspensionFormula_zero_raw]
  simp only [unshiftedHomLevelIso, eqToIso.hom]
  erw [← eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add (q + 1))),
    ← eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add q))]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    shiftedHomSuspensionIndex_zero]
  erw [eqToHom_map]
  rw [eqToHom_trans]
  exact unshiftedHomSuspensionFormula_index_eq X E (Nat.zero_add q)

/-- 生成次数零の各段の比較は、実際の構造射を通常の内部Homの直接公式へ移す。 -/
@[reassoc]
lemma unshiftedHomLevelIso_structureMap (p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    structureMap (shiftedHom 0 X E) p q ≫ (unshiftedHomLevelIso (p + q) X E).hom =
      (𝟙 (TensorPowers.power K p) ⊗ₘ (unshiftedHomLevelIso q X E).hom) ≫
        unshiftedHomStructureFormula p q X E := by
  rw [shiftedHom_structureMap_eq_formula]
  exact shiftedHomStructureFormula_zero p q X E

/-- 生成次数零の各段の比較は、実際の懸垂射も通常の内部Homの直接公式へ移す。 -/
@[reassoc]
lemma unshiftedHomLevelIso_suspensionMap (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    suspensionMap (shiftedHom 0 X E) q ≫ (unshiftedHomLevelIso (q + 1) X E).hom =
      K ◁ (unshiftedHomLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  rw [shiftedHom_suspensionMap_eq_formula]
  exact shiftedHomSuspensionFormula_zero q X E

/-- F_0からの内部Homの第q段を、値域の同じ第q段への通常の内部Homへ比較する。 -/
def internalHomFreeZeroLevelIso (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    level (internalHom ((freeAt 0).obj X) E) q ≅ (ihom X).obj (level E q) :=
  internalHomFreeAtLevelIso 0 q X E ≪≫ unshiftedHomLevelIso q X E

/-- F_0からの内部Homの構造射は添字の置換を含まない直接公式へ移る。 -/
@[reassoc]
lemma internalHomFreeZeroLevelIso_structureMap (p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    structureMap (internalHom ((freeAt 0).obj X) E) p q ≫
        (internalHomFreeZeroLevelIso (p + q) X E).hom =
      (𝟙 (TensorPowers.power K p) ⊗ₘ (internalHomFreeZeroLevelIso q X E).hom) ≫
        unshiftedHomStructureFormula p q X E := by
  unfold internalHomFreeZeroLevelIso
  simp only [Iso.trans_hom]
  have h := structureMap_hom (internalHomShiftIso 0 X E).hom p q
  change structureMap (internalHom ((freeAt 0).obj X) E) p q ≫
      (internalHomFreeAtLevelIso 0 (p + q) X E).hom =
    (𝟙 (TensorPowers.power K p) ⊗ₘ (internalHomFreeAtLevelIso 0 q X E).hom) ≫
      structureMap (shiftedHom 0 X E) p q at h
  erw [reassoc_of% h, unshiftedHomLevelIso_structureMap]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

/-- F_0からの内部Homの懸垂射も添字の置換を含まない直接公式へ移る。 -/
@[reassoc]
lemma internalHomFreeZeroLevelIso_suspensionMap (q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    suspensionMap (internalHom ((freeAt 0).obj X) E) q ≫
        (internalHomFreeZeroLevelIso (q + 1) X E).hom =
      K ◁ (internalHomFreeZeroLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  unfold internalHomFreeZeroLevelIso
  simp only [Iso.trans_hom]
  have h := suspensionMap_hom (internalHomShiftIso 0 X E).hom q
  change suspensionMap (internalHom ((freeAt 0).obj X) E) q ≫
      (internalHomFreeAtLevelIso 0 (q + 1) X E).hom =
    K ◁ (internalHomFreeAtLevelIso 0 q X E).hom ≫ suspensionMap (shiftedHom 0 X E) q at h
  erw [reassoc_of% h, unshiftedHomLevelIso_suspensionMap]
  rw [← whiskerLeft_comp_assoc]

end SerrePositivity.GeneralSymmetricSpectrum
