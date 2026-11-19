module

public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomShiftStructure

/-! # 次数をずらした内部Homの懸垂構造射の直接公式

円による懸垂と値域の懸垂を、生成元のブロックを越える添字の交換で結ぶ。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 懸垂後の添字を、円の要素を生成元の後ろへ移した添字に交換する。 -/
def shiftedHomSuspensionIndex (n q : ℕ) :
    FiniteBijection.of ((n + q) + 1) ⟶ FiniteBijection.of (n + (q + 1)) :=
  eqToHom (congrArg FiniteBijection.of (Nat.one_add (n + q)).symm) ≫
    shiftedHomStructureIndex n 1 q ≫
      eqToHom (congrArg FiniteBijection.of (congrArg (n + ·) (Nat.one_add q)))

/-- 次数の等式による内部Homの移送は、評価の後の値域の移送に一致する。 -/
@[reassoc]
lemma shiftedHom_evaluation_index_eq (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) {a b : ℕ} (h : a = b) :
    X ◁ eqToHom (congrArg (level (shiftedHom n X E)) h) ≫
        (ihom.ev X).app (level E (n + b)) =
      (ihom.ev X).app (level E (n + a)) ≫
        eqToHom (congrArg (level E) (congrArg (n + ·) h)) := by
  subst b
  simp

/-- 内部Homの次数移送は値域の次数移送による後合成。 -/
lemma shiftedHom_index_eq_ihom_map (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (level (shiftedHom n X E)) h) =
      (ihom X).map (eqToHom (congrArg (level E) (congrArg (n + ·) h))) := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- 値域の懸垂とブロック交換を、第一球面の構造射と次数移送で表示する。 -/
lemma suspensionMap_shiftedIndex (n q : ℕ) (E : SymmetricSpectrum.{u}) :
    suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q) =
      (spherePowerOneIso.{u}).inv ▷ level E (n + q) ≫
        structureMap E 1 (n + q) ≫ E.X.map (shiftedHomStructureIndex n 1 q) ≫
          eqToHom (congrArg (level E) (congrArg (n + ·) (Nat.one_add q))) := by
  unfold suspensionMap shiftedHomSuspensionIndex
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  erw [eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- 通常の評価を介した、値域の懸垂構造射による直接公式。 -/
@[reassoc]
lemma shiftedHom_suspensionMap_evaluation (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    X ◁ suspensionMap (shiftedHom n X E) q ≫
        (ihom.ev X).app (level E (n + (q + 1))) =
      (α_ X (circle : PointedSimplicialSet.{u}) (level (shiftedHom n X E) q)).inv ≫
        (β_ X (circle : PointedSimplicialSet.{u})).hom ▷ level (shiftedHom n X E) q ≫
          (α_ (circle : PointedSimplicialSet.{u}) X (level (shiftedHom n X E) q)).hom ≫
            (circle : PointedSimplicialSet.{u}) ◁ (ihom.ev X).app (level E (n + q)) ≫
              suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q) := by
  rw [suspensionMap_shiftedIndex]
  unfold suspensionMap
  change X ◁ ((spherePowerOneIso.{u}).inv ▷ level (shiftedHom n X E) q ≫
      structureMap (shiftedHom n X E) 1 q ≫
        eqToHom (congrArg (level (shiftedHom n X E)) (Nat.one_add q))) ≫
      (ihom.ev X).app (level E (n + (q + 1))) = _
  simp only [whiskerLeft_comp, Category.assoc]
  rw [shiftedHom_evaluation_index_eq n X E (Nat.one_add q)]
  rw [shiftedHom_structureMap_evaluation_assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]

/-- 懸垂構造射を値域の懸垂・通常の評価・添字の交換から直接作る。 -/
def shiftedHomSuspensionFormula (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (circle : PointedSimplicialSet.{u}) ⊗ (ihom X).obj (level E (n + q)) ⟶
      (ihom X).obj (level E (n + (q + 1))) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (circle : PointedSimplicialSet.{u}) ((ihom X).obj (level E (n + q)))).inv ≫
      (β_ X (circle : PointedSimplicialSet.{u})).hom ▷ (ihom X).obj (level E (n + q)) ≫
        (α_ (circle : PointedSimplicialSet.{u}) X ((ihom X).obj (level E (n + q)))).hom ≫
          (circle : PointedSimplicialSet.{u}) ◁ (ihom.ev X).app (level E (n + q)) ≫
            suspensionMap E (n + q) ≫ E.X.map (shiftedHomSuspensionIndex n q))

/-- 次数をずらした内部Homの懸垂構造射は直接公式に一致する。 -/
lemma shiftedHom_suspensionMap_eq_formula (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (shiftedHom n X E) q = shiftedHomSuspensionFormula n q X E := by
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  unfold shiftedHomSuspensionFormula
  rw [CategoryTheory.MonoidalClosed.uncurry_curry, CategoryTheory.MonoidalClosed.uncurry_eq]
  exact shiftedHom_suspensionMap_evaluation n q X E

/-- 懸垂の直接公式は第一球面の直接公式を円へ移し、値域の次数を後合成で移した射。 -/
lemma shiftedHomSuspensionFormula_eq_structureFormula (n q : ℕ)
    (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    shiftedHomSuspensionFormula n q X E =
      (spherePowerOneIso.{u}).inv ▷ (ihom X).obj (level E (n + q)) ≫
        shiftedHomStructureFormula n 1 q X E ≫
          (ihom X).map
            (eqToHom (congrArg (level E) (congrArg (n + ·) (Nat.one_add q)))) := by
  rw [← shiftedHom_suspensionMap_eq_formula]
  unfold suspensionMap
  rw [shiftedHom_structureMap_eq_formula,
    shiftedHom_index_eq_ihom_map n X E (Nat.one_add q)]
  rfl

/-- F_nからの内部Homの懸垂も、各段の比較と値域の懸垂の直接公式で計算できる。 -/
lemma internalHomFreeAt_suspensionMap_formula (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (internalHom ((freeAt n).obj X) E) q =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (internalHomFreeAtLevelIso n q X E).hom ≫
          shiftedHomSuspensionFormula n q X E ≫ (internalHomFreeAtLevelIso n (q + 1) X E).inv := by
  apply (cancel_mono (internalHomFreeAtLevelIso n (q + 1) X E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← shiftedHom_suspensionMap_eq_formula]
  exact internalHomFreeAtLevelIso_suspensionMap n q X E

end SerrePositivity.SymmetricSpectrum
