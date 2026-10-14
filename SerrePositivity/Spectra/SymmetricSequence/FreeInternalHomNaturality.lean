module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomSequenceIso

/-! # 自由原変数の内部Homの各段の両変数自然性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

omit [HasLimitsOfSize.{0, 0} C] in
/-- 和次数の自由生成の逆比較は第一の生成対象の射に関して自然。 -/
@[reassoc]
lemma freePairConvolutionIso_inv_naturality_left (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    (Z : C) :
    (freePairConvolutionIso n m X Z).inv ≫ (freeAt n).map f ▷ (freeAt m).obj Z =
      (freeAt (n + m)).map (f ▷ Z) ≫ (freePairConvolutionIso n m Y Z).inv := by
  apply (cancel_mono (freePairConvolutionIso n m Y Z).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := freePairConvolutionIso_naturality n m f (𝟙 Z)
  erw [CategoryTheory.Functor.map_id] at h
  simp only [tensorHom_id] at h
  erw [h, Iso.inv_hom_id_assoc]

/-- 各段のHom同値は自由生成対象の射に関して反変自然。 -/
lemma freeInternalHomLevelEquiv_naturality_source (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    (F : SymmetricSequence C) {Z : C}
    (k : Z ⟶ level ((ihom ((freeAt n).obj Y)).obj F) m) :
    freeInternalHomLevelEquiv n m X F Z
        (k ≫ ((pre ((freeAt n).map f)).app F).app (FiniteBijection.of m)) =
      freeInternalHomLevelEquiv n m Y F Z k ≫ (pre f).app (level F (n + m)) := by
  rw [freeInternalHomLevelEquiv_apply, freeInternalHomLevelEquiv_apply]
  have h := (freeAtAdjunction (C := C) m).homEquiv_naturality_right_symm k
    ((pre ((freeAt n).map f)).app F)
  erw [h, uncurry_pre_app]
  change curry ((freeAtAdjunction (n + m)).homEquiv _ F
    ((freePairConvolutionIso n m X Z).inv ≫
      (freeAt n).map f ▷ (freeAt m).obj Z ≫ uncurry _)) = _
  rw [freePairConvolutionIso_inv_naturality_left_assoc,
    (freeAtAdjunction (n + m)).homEquiv_naturality_left, ← curry_pre_app]
  rfl

/-- 各段の比較は自由生成対象の射に関して反変自然。 -/
@[reassoc]
lemma freeInternalHomLevelIso_naturality_source (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    (F : SymmetricSequence C) :
    ((pre ((freeAt n).map f)).app F).app (FiniteBijection.of m) ≫
        (freeInternalHomLevelIso n m X F).hom =
      (freeInternalHomLevelIso n m Y F).hom ≫ (pre f).app (level F (n + m)) := by
  have h := freeInternalHomLevelEquiv_naturality_source n m f F (𝟙 _)
  have h' := freeInternalHomLevelEquiv_naturality n m X F
    (((pre ((freeAt n).map f)).app F).app (FiniteBijection.of m)) (𝟙 _)
  simp only [Category.id_comp, Category.comp_id] at h h'
  exact h'.symm.trans h

/-- 次数をずらした内部Homの射は、各段で前合成してから後合成する射。 -/
def shiftedInternalHomMap (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    shiftedInternalHom n Y F ⟶ shiftedInternalHom n X G :=
  CategoryTheory.Functor.whiskerLeft
    (tensorLeft (FiniteBijection.of n) ⋙ toFunctorCategory.obj F) (pre f) ≫
    CategoryTheory.Functor.whiskerRight
      (CategoryTheory.Functor.whiskerLeft
        (tensorLeft (FiniteBijection.of n)) (toFunctorCategory.map g)) (ihom X)

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- 次数をずらした内部Homの射の各段の成分。 -/
lemma shiftedInternalHomMap_app (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    (shiftedInternalHomMap n f g).app (FiniteBijection.of m) =
      (pre f).app (level F (n + m)) ≫ (ihom X).map (g.app (FiniteBijection.of (n + m))) := by
  rfl

/-- 対称列全体の比較は生成対象に反変、値域に共変な射に関して自然。 -/
@[reassoc]
lemma freeInternalHomSequenceIso_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    (pre ((freeAt n).map f)).app F ≫ (ihom ((freeAt n).obj X)).map g ≫
        (freeInternalHomSequenceIso n X G).hom =
      (freeInternalHomSequenceIso n Y F).hom ≫ shiftedInternalHomMap n f g := by
  apply NatTrans.ext
  funext a
  rw [← FiniteBijection.of_card a]
  change ((pre ((freeAt n).map f)).app F).app (FiniteBijection.of a.card) ≫
      ((ihom ((freeAt n).obj X)).map g).app (FiniteBijection.of a.card) ≫
        (freeInternalHomLevelIso n a.card X G).hom =
    (freeInternalHomLevelIso n a.card Y F).hom ≫
      (shiftedInternalHomMap n f g).app (FiniteBijection.of a.card)
  rw [freeInternalHomLevelIso_naturality, freeInternalHomLevelIso_naturality_source_assoc,
    shiftedInternalHomMap_app]

/-- 対称列の射を比較の順逆で移すと、各段の通常の前合成・後合成に一致する。 -/
lemma freeInternalHomSequenceIso_conjugate (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    (freeInternalHomSequenceIso n Y F).inv ≫ (pre ((freeAt n).map f)).app F ≫
        (ihom ((freeAt n).obj X)).map g ≫ (freeInternalHomSequenceIso n X G).hom =
      shiftedInternalHomMap n f g := by
  rw [freeInternalHomSequenceIso_naturality]
  simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.SymmetricSequence
