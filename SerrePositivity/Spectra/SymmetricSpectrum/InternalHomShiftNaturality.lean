module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomModuleNaturality
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomShiftSuspension

/-! # 次数をずらした内部Homの射と構造射の直接公式の自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap_hom)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 生成対象に反変、値域スペクトルに共変な次数をずらした内部Homの射。 -/
def shiftedHomMap (n : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : shiftedHom n Y E ⟶ shiftedHom n X F :=
  SymmetricSequence.freeShiftModuleMap sphereSequence.{u} n f g

/-- スペクトルの射の基礎射は、各段の通常の内部Homの前合成と後合成。 -/
lemma shiftedHomMap_hom (n : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (shiftedHomMap n f g).hom = SymmetricSequence.shiftedInternalHomMap n f g.hom :=
  SymmetricSequence.freeShiftModuleMap_hom
    (C := PointedSimplicialSet.{u}) sphereSequence.{u} n f g

/-- 次数をずらした内部Homの第m段の射を通常の前合成・後合成で記述する。 -/
def shiftedHomLevelMap (n m : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (ihom Y).obj (level E (n + m)) ⟶ (ihom X).obj (level F (n + m)) :=
  (pre f).app (level E (n + m)) ≫ (ihom X).map (g.hom.app (FiniteBijection.of (n + m)))

/-- スペクトル射の成分は各段の通常の内部Homの射。 -/
lemma shiftedHomMap_app (n m : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (shiftedHomMap n f g).hom.app (FiniteBijection.of m) = shiftedHomLevelMap n m f g := by
  rw [shiftedHomMap_hom, SymmetricSequence.shiftedInternalHomMap_app]
  rfl

/-- 値域の構造射による直接公式は、通常の前合成・後合成と両立する。 -/
@[reassoc]
lemma shiftedHomStructureFormula_naturality (n p q : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    shiftedHomStructureFormula n p q Y E ≫ shiftedHomLevelMap n (p + q) f g =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (shiftedHomLevelMap n q f g) ≫
        shiftedHomStructureFormula n p q X F := by
  have h := structureMap_hom (shiftedHomMap n f g) p q
  change _ = PointedObject.smashMap (𝟙 (spherePower.{u} p))
    ((shiftedHomMap n f g).hom.app (FiniteBijection.of q)) ≫ _ at h
  simpa only [shiftedHom_structureMap_eq_formula, shiftedHomMap_app] using h

/-- 値域の懸垂による直接公式も、通常の前合成・後合成と両立する。 -/
@[reassoc]
lemma shiftedHomSuspensionFormula_naturality (n q : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    shiftedHomSuspensionFormula n q Y E ≫ shiftedHomLevelMap n (q + 1) f g =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (shiftedHomLevelMap n q f g) ≫ shiftedHomSuspensionFormula n q X F := by
  have h := suspensionMap_hom (shiftedHomMap n f g) q
  simpa only [shiftedHom_suspensionMap_eq_formula, shiftedHomMap_app] using h

end SerrePositivity.SymmetricSpectrum
