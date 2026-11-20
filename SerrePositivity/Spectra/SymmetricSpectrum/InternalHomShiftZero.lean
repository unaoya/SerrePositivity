module

public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionMiddleExchangeUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomShiftNaturality

/-! # 生成次数零の内部Homの各段と直接公式 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 生成次数零の構造射の添字交換は、零加法の移送だけになる。 -/
lemma shiftedHomStructureIndex_zero (p q : ℕ) :
    shiftedHomStructureIndex 0 p q =
      eqToHom (congrArg FiniteBijection.of
        ((congrArg (p + ·) (Nat.zero_add q)).trans (Nat.zero_add (p + q)).symm)) :=
  SymmetricSequence.middleExchangeIndex_zero p q

/-- 生成次数零の懸垂では、次数の移送の他に置換は入らない。 -/
lemma shiftedHomSuspensionIndex_zero (q : ℕ) :
    shiftedHomSuspensionIndex 0 q =
      eqToHom (congrArg FiniteBijection.of
        ((congrArg (· + 1) (Nat.zero_add q)).trans (Nat.zero_add (q + 1)).symm)) := by
  unfold shiftedHomSuspensionIndex
  rw [shiftedHomStructureIndex_zero]
  simp only [eqToHom_trans]

/-- 生成次数零の第q段は、そのまま第q段への通常の内部Hom。 -/
def unshiftedHomLevelIso (q : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    level (shiftedHom 0 X E) q ≅ (ihom X).obj (level E q) :=
  eqToIso (congrArg (fun k => (ihom X).obj (level E k)) (Nat.zero_add q))

/-- 添字の置換を使わず値域の構造射から作る通常の内部Homの構造射。 -/
def unshiftedHomStructureFormula (p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    spherePower.{u} p ⊗ (ihom X).obj (level E q) ⟶ (ihom X).obj (level E (p + q)) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (spherePower.{u} p) ((ihom X).obj (level E q))).inv ≫
      (β_ X (spherePower.{u} p)).hom ▷ (ihom X).obj (level E q) ≫
        (α_ (spherePower.{u} p) X ((ihom X).obj (level E q))).hom ≫
          spherePower.{u} p ◁ (ihom.ev X).app (level E q) ≫ structureMap E p q)

/-- 第零生成次数の比較の順射は値域の次数移送による後合成。 -/
lemma unshiftedHomLevelIso_hom (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (unshiftedHomLevelIso q X E).hom =
      (ihom X).map (eqToHom (congrArg (level E) (Nat.zero_add q))) := by
  erw [eqToHom_map]
  rfl

/-- 通常の内部Homの構造射の直接公式は次数の等式による移送と両立する。 -/
lemma unshiftedHomStructureFormula_index_eq (p : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) {a b : ℕ} (h : a = b) :
    unshiftedHomStructureFormula p a X E ≫
        (ihom X).map (eqToHom (congrArg (level E) (congrArg (p + ·) h))) =
      PointedObject.smashMap (𝟙 (spherePower.{u} p))
        ((ihom X).map (eqToHom (congrArg (level E) h))) ≫
          unshiftedHomStructureFormula p b X E := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id,
    PointedObject.smashMap_id, Category.id_comp, Category.comp_id]

/-- 構造射の生成次数零への特殊化を、添字の移送の後合成で表示する。 -/
lemma shiftedHomStructureFormula_zero_raw (p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    shiftedHomStructureFormula 0 p q X E =
      unshiftedHomStructureFormula p (0 + q) X E ≫
        (ihom X).map (E.X.map (shiftedHomStructureIndex 0 p q)) := by
  unfold shiftedHomStructureFormula unshiftedHomStructureFormula
  rw [← CategoryTheory.MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

/-- 生成次数零の構造射の直接公式は通常の内部Homの構造射に移る。 -/
lemma shiftedHomStructureFormula_zero (p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    shiftedHomStructureFormula 0 p q X E ≫ (unshiftedHomLevelIso (p + q) X E).hom =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (unshiftedHomLevelIso q X E).hom ≫
        unshiftedHomStructureFormula p q X E := by
  rw [shiftedHomStructureFormula_zero_raw, unshiftedHomLevelIso_hom,
    unshiftedHomLevelIso_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    shiftedHomStructureIndex_zero]
  erw [eqToHom_map]
  rw [eqToHom_trans]
  exact unshiftedHomStructureFormula_index_eq p X E (Nat.zero_add q)

/-- 円による通常の内部Homの懸垂も、値域の懸垂と評価から直接作る。 -/
def unshiftedHomSuspensionFormula (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (circle : PointedSimplicialSet.{u}) ⊗ (ihom X).obj (level E q) ⟶
      (ihom X).obj (level E (q + 1)) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (circle : PointedSimplicialSet.{u}) ((ihom X).obj (level E q))).inv ≫
      (β_ X (circle : PointedSimplicialSet.{u})).hom ▷ (ihom X).obj (level E q) ≫
        (α_ (circle : PointedSimplicialSet.{u}) X ((ihom X).obj (level E q))).hom ≫
          (circle : PointedSimplicialSet.{u}) ◁ (ihom.ev X).app (level E q) ≫ suspensionMap E q)

/-- 通常の内部Homの懸垂の直接公式も次数の等式による移送と両立する。 -/
lemma unshiftedHomSuspensionFormula_index_eq (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) {a b : ℕ} (h : a = b) :
    unshiftedHomSuspensionFormula a X E ≫
        (ihom X).map (eqToHom (congrArg (level E) (congrArg (· + 1) h))) =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        ((ihom X).map (eqToHom (congrArg (level E) h))) ≫
          unshiftedHomSuspensionFormula b X E := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id,
    PointedObject.smashMap_id, Category.id_comp, Category.comp_id]

/-- 懸垂の生成次数零への特殊化を、添字の移送の後合成で表示する。 -/
lemma shiftedHomSuspensionFormula_zero_raw (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    shiftedHomSuspensionFormula 0 q X E =
      unshiftedHomSuspensionFormula (0 + q) X E ≫
        (ihom X).map (E.X.map (shiftedHomSuspensionIndex 0 q)) := by
  unfold shiftedHomSuspensionFormula unshiftedHomSuspensionFormula
  rw [← CategoryTheory.MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

/-- 生成次数零の懸垂の直接公式は通常の内部Homの懸垂に移る。 -/
lemma shiftedHomSuspensionFormula_zero (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    shiftedHomSuspensionFormula 0 q X E ≫ (unshiftedHomLevelIso (q + 1) X E).hom =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (unshiftedHomLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  rw [shiftedHomSuspensionFormula_zero_raw, unshiftedHomLevelIso_hom,
    unshiftedHomLevelIso_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    shiftedHomSuspensionIndex_zero]
  erw [eqToHom_map]
  rw [eqToHom_trans]
  exact unshiftedHomSuspensionFormula_index_eq X E (Nat.zero_add q)

/-- 生成次数零の各段の比較は、実際の構造射を通常の内部Homの直接公式へ移す。 -/
@[reassoc]
lemma unshiftedHomLevelIso_structureMap (p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (shiftedHom 0 X E) p q ≫ (unshiftedHomLevelIso (p + q) X E).hom =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (unshiftedHomLevelIso q X E).hom ≫
        unshiftedHomStructureFormula p q X E := by
  rw [shiftedHom_structureMap_eq_formula]
  exact shiftedHomStructureFormula_zero p q X E

/-- 生成次数零の各段の比較は、実際の懸垂射も通常の内部Homの直接公式へ移す。 -/
@[reassoc]
lemma unshiftedHomLevelIso_suspensionMap (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (shiftedHom 0 X E) q ≫ (unshiftedHomLevelIso (q + 1) X E).hom =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (unshiftedHomLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  rw [shiftedHom_suspensionMap_eq_formula]
  exact shiftedHomSuspensionFormula_zero q X E

/-- F_0からの内部Homの第q段を、値域の同じ第q段への通常の内部Homへ比較する。 -/
def internalHomFreeZeroLevelIso (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    level (internalHom ((freeAt 0).obj X) E) q ≅ (ihom X).obj (level E q) :=
  internalHomFreeAtLevelIso 0 q X E ≪≫ unshiftedHomLevelIso q X E

/-- F_0からの内部Homの構造射は添字の置換を含まない直接公式へ移る。 -/
@[reassoc]
lemma internalHomFreeZeroLevelIso_structureMap (p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (internalHom ((freeAt 0).obj X) E) p q ≫
        (internalHomFreeZeroLevelIso (p + q) X E).hom =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (internalHomFreeZeroLevelIso q X E).hom ≫
        unshiftedHomStructureFormula p q X E := by
  unfold internalHomFreeZeroLevelIso
  simp only [Iso.trans_hom]
  rw [reassoc_of% (internalHomFreeAtLevelIso_structureMap 0 p q X E),
    unshiftedHomLevelIso_structureMap]
  rw [← Category.assoc, PointedObject.smashMap_comp, Category.id_comp]

/-- F_0からの内部Homの懸垂射も添字の置換を含まない直接公式へ移る。 -/
@[reassoc]
lemma internalHomFreeZeroLevelIso_suspensionMap (q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (internalHom ((freeAt 0).obj X) E) q ≫
        (internalHomFreeZeroLevelIso (q + 1) X E).hom =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (internalHomFreeZeroLevelIso q X E).hom ≫ unshiftedHomSuspensionFormula q X E := by
  unfold internalHomFreeZeroLevelIso
  simp only [Iso.trans_hom]
  rw [reassoc_of% (internalHomFreeAtLevelIso_suspensionMap 0 q X E),
    unshiftedHomLevelIso_suspensionMap]
  rw [← Category.assoc, PointedObject.smashMap_comp, Category.id_comp]

end SerrePositivity.SymmetricSpectrum
