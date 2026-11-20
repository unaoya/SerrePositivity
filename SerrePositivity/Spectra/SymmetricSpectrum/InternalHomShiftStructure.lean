module

import SerrePositivity.Spectra.General.ShiftedHom
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomShiftEvaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomShift

/-! # 次数をずらした内部Homの構造射と値域の構造射

通常の内部Homの評価を介し、構造射を値域の構造射と添字のブロック交換から記述する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action level structureMap)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面のp要素を生成元のn要素の後ろへ戻す添字の射。 -/
def shiftedHomStructureIndex (n p q : ℕ) :
    FiniteBijection.of (p + (n + q)) ⟶ FiniteBijection.of (n + (p + q)) :=
  SymmetricSequence.middleExchangeIndex (FiniteBijection.of n)
    (FiniteBijection.of p) (FiniteBijection.of q)

/-- スペクトルの構造射は一般のconvolutionの次数成分に一致する。 -/
lemma structureMap_eq_convolutionComponent (E : SymmetricSpectrum.{u}) (p q : ℕ) :
    structureMap E p q =
      SymmetricSequence.convolutionComponent (action E)
        (FiniteBijection.of p) (FiniteBijection.of q) := by
  rfl

/-- 次数をずらしたスペクトルは一般の係数加群の構成の球面特殊化。 -/
lemma shiftedHom_eq_freeShiftModule (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    shiftedHom n X E = SymmetricSequence.freeShiftModule sphereSequence.{u} n X E := by
  rfl

/-- 移送後のスペクトルの構造射を一般の係数加群の次数成分へ接続する。 -/
lemma shiftedHom_structureMap_eq_component (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (shiftedHom n X E) p q =
      SymmetricSequence.convolutionComponent
        (action (SymmetricSequence.freeShiftModule sphereSequence.{u} n X E))
        (FiniteBijection.of p) (FiniteBijection.of q) := by
  have hd : ∀ (A B : SymmetricSpectrum.{u}), A = B →
      HEq (structureMap A p q) (structureMap B p q) := by
    intro A B h
    cases h
    rfl
  have h := eq_of_heq (hd _ _ (shiftedHom_eq_freeShiftModule n X E))
  exact h.trans (structureMap_eq_convolutionComponent _ p q)

/-- 値域の構造射による次数をずらした内部Homの構造射の評価公式。 -/
@[reassoc]
lemma shiftedHom_structureMap_evaluation (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    X ◁ structureMap (shiftedHom n X E) p q ≫
        (ihom.ev X).app (level E (n + (p + q))) =
      (α_ X (spherePower.{u} p) (level (shiftedHom n X E) q)).inv ≫
        (β_ X (spherePower.{u} p)).hom ▷ level (shiftedHom n X E) q ≫
          (α_ (spherePower.{u} p) X (level (shiftedHom n X E) q)).hom ≫
            spherePower.{u} p ◁ (ihom.ev X).app (level E (n + q)) ≫
              structureMap E p (n + q) ≫ E.X.map (shiftedHomStructureIndex n p q) := by
  exact GeneralSymmetricSpectrum.shiftedHom_structureMap_evaluation (K := circle.{u}) n p q X E

/-- 値域の構造射・評価・ブロック交換から直接作る内部Homの構造射。 -/
def shiftedHomStructureFormula (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    spherePower.{u} p ⊗ (ihom X).obj (level E (n + q)) ⟶
      (ihom X).obj (level E (n + (p + q))) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (spherePower.{u} p) ((ihom X).obj (level E (n + q)))).inv ≫
      (β_ X (spherePower.{u} p)).hom ▷ (ihom X).obj (level E (n + q)) ≫
        (α_ (spherePower.{u} p) X ((ihom X).obj (level E (n + q)))).hom ≫
          spherePower.{u} p ◁ (ihom.ev X).app (level E (n + q)) ≫
            structureMap E p (n + q) ≫ E.X.map (shiftedHomStructureIndex n p q))

/-- 次数をずらした内部Homの構造射は値域の構造射から直接作った射に一致する。 -/
lemma shiftedHom_structureMap_eq_formula (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (shiftedHom n X E) p q = shiftedHomStructureFormula n p q X E := by
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  unfold shiftedHomStructureFormula
  rw [CategoryTheory.MonoidalClosed.uncurry_curry, CategoryTheory.MonoidalClosed.uncurry_eq]
  exact shiftedHom_structureMap_evaluation n p q X E

/-- F_nからの内部Homの構造射も各段の比較と値域の構造射の直接公式で計算できる。 -/
lemma internalHomFreeAt_structureMap_formula (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (internalHom ((freeAt n).obj X) E) p q =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (internalHomFreeAtLevelIso n q X E).hom ≫
        shiftedHomStructureFormula n p q X E ≫ (internalHomFreeAtLevelIso n (p + q) X E).inv := by
  apply (cancel_mono (internalHomFreeAtLevelIso n (p + q) X E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← shiftedHom_structureMap_eq_formula]
  exact internalHomFreeAtLevelIso_structureMap n p q X E

end SerrePositivity.SymmetricSpectrum
