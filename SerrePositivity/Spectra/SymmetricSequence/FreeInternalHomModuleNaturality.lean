module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomNaturality
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomShiftEvaluation

/-! # 次数をずらした内部Homの係数加群としての自然性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]

variable (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 自由原変数との比較を次数をずらした内部Homとの加群比較へ合成する。 -/
def freeShiftModuleIso (n : ℕ) (X : C) (F : Mod (SymmetricSequence C) M) :=
  MonoidalModuleInternalHom.freeHomModuleIso M ((freeAt n).obj X) F ≪≫
    MonoidalModuleInternalHom.transportedIso M ((freeAt n).obj X) F
      (freeInternalHomSequenceIso n X F.X)

/-- 生成対象に反変、値域加群に共変な次数をずらした内部Homの加群射。 -/
def freeShiftModuleMap (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : Mod (SymmetricSequence C) M} (g : F ⟶ G) :
    freeShiftModule M n Y F ⟶ freeShiftModule M n X G :=
  (MonoidalModuleInternalHom.transportedIso M ((freeAt n).obj Y) F
    (freeInternalHomSequenceIso n Y F.X)).inv ≫
      MonoidalModuleInternalHom.freeHomMap M ((freeAt n).map f) g ≫
        (MonoidalModuleInternalHom.transportedIso M ((freeAt n).obj X) G
          (freeInternalHomSequenceIso n X G.X)).hom

/-- 次数をずらした内部Homの加群射の基礎射は、対称列の前合成・後合成。 -/
lemma freeShiftModuleMap_hom (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : Mod (SymmetricSequence C) M} (g : F ⟶ G) :
    (freeShiftModuleMap M n f g).hom = shiftedInternalHomMap n f g.hom := by
  unfold freeShiftModuleMap
  simp only [Mod.comp_hom']
  rw [MonoidalModuleInternalHom.freeHomMap_hom]
  change (freeInternalHomSequenceIso n Y F.X).inv ≫
      ((pre ((freeAt n).map f)).app F.X ≫ (ihom ((freeAt n).obj X)).map g.hom) ≫
        (freeInternalHomSequenceIso n X G.X).hom = _
  simp only [Category.assoc]
  exact freeInternalHomSequenceIso_conjugate n f g.hom

/-- 自由原変数との加群比較は両変数に自然。 -/
@[reassoc]
lemma freeShiftModuleIso_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : Mod (SymmetricSequence C) M} (g : F ⟶ G) :
    MonoidalModuleInternalHom.homMap M
        (MonoidalFreeModule.freeMap M ((freeAt n).map f)) g ≫
      (freeShiftModuleIso M n X G).hom =
    (freeShiftModuleIso M n Y F).hom ≫ freeShiftModuleMap M n f g := by
  unfold freeShiftModuleIso freeShiftModuleMap
  simp only [Iso.trans_hom, Category.assoc]
  rw [MonoidalModuleInternalHom.freeHomModuleIso_naturality_assoc]
  simp only [Iso.hom_inv_id_assoc]

/-- 加群射の第m段は、通常の内部Homの前合成・後合成。 -/
lemma freeShiftModuleMap_app (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : Mod (SymmetricSequence C) M} (g : F ⟶ G) :
    (freeShiftModuleMap M n f g).hom.app (FiniteBijection.of m) =
      (pre f).app (level F.X (n + m)) ≫
        (ihom X).map (g.hom.app (FiniteBijection.of (n + m))) := by
  rw [freeShiftModuleMap_hom, shiftedInternalHomMap_app]

/-- 自由原変数との加群比較の自然性を各段の成分で記述する。 -/
@[reassoc]
lemma freeShiftModuleIso_app_naturality (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : Mod (SymmetricSequence C) M} (g : F ⟶ G) :
    (MonoidalModuleInternalHom.homMap M
        (MonoidalFreeModule.freeMap M ((freeAt n).map f)) g).hom.app (FiniteBijection.of m) ≫
      (freeShiftModuleIso M n X G).hom.hom.app (FiniteBijection.of m) =
    (freeShiftModuleIso M n Y F).hom.hom.app (FiniteBijection.of m) ≫
      ((pre f).app (level F.X (n + m)) ≫
        (ihom X).map (g.hom.app (FiniteBijection.of (n + m)))) := by
  have h := congrArg (fun k => k.hom.app (FiniteBijection.of m))
    (freeShiftModuleIso_naturality M n f g)
  change (MonoidalModuleInternalHom.homMap M
      (MonoidalFreeModule.freeMap M ((freeAt n).map f)) g).hom.app (FiniteBijection.of m) ≫
    (freeShiftModuleIso M n X G).hom.hom.app (FiniteBijection.of m) =
    (freeShiftModuleIso M n Y F).hom.hom.app (FiniteBijection.of m) ≫
      (freeShiftModuleMap M n f g).hom.app (FiniteBijection.of m) at h
  rw [freeShiftModuleMap_app] at h
  exact h

end SerrePositivity.SymmetricSequence
