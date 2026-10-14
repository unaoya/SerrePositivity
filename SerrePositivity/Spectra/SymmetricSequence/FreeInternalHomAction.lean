module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHom

/-! # 自由原変数の内部Homの各段の置換作用

各段の比較をendの射影で記述し、後ろのブロックの置換との両立を証明する。
-/

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

/-- convolutionの標準射上で、評価はendの射影の逆転置に一致する。 -/
@[reassoc]
lemma convolutionUnit_evaluation (F G : SymmetricSequence C) (x y : FiniteBijection) :
    (convolutionUnit F ((ihom F).obj G)).app (x, y) ≫
      ((ihom.ev F).app G).app (x ⊗ y) = uncurry (internalHomProjection F G y x) := by
  let : DayConvolution (toFunctorCategory.obj F)
      (toFunctorCategory.obj ((internalHomFunctor F).obj G)) :=
    canonicalDayConvolution F ((internalHomFunctor F).obj G)
  have h := (dayInternalHom F G).unit_app_ev_app_app x y
  change (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
      FiniteBijection C F ((ihom F).obj G)).app (x, y) ≫
    (convolutionEvaluation F G).app (x ⊗ y) = _ at h
  rw [lawfulConvolutionExtensionUnit_app] at h
  exact h

/-- 各段の比較は自由生成元へ制限したendの射影。 -/
lemma freeInternalHomLevelIso_hom_projection (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    (freeInternalHomLevelIso n m X F).hom =
      internalHomProjection ((freeAt n).obj X) F (FiniteBijection.of m) (FiniteBijection.of n) ≫
        (pre (freeAtGenerator n X)).app (level F (n + m)) := by
  change freeInternalHomLevelEquiv n m X F _ (𝟙 _) = _
  rw [freeInternalHomLevelEquiv_apply, freeAtHomEquiv_apply]
  erw [NatTrans.comp_app]
  erw [freePairConvolutionIso_generator_inv_assoc]
  rw [uncurry_eq]
  change curry (freePairConvolutionGenerator n m X _ ≫
    (((freeAt n).obj X ◁ freeAtLift m _ (𝟙 _)) ≫
      (ihom.ev ((freeAt n).obj X)).app F).app (FiniteBijection.of (n + m))) = _
  unfold freePairConvolutionGenerator
  erw [NatTrans.comp_app, Category.assoc, convolutionUnit_whiskerLeft_assoc]
  simp only [tensorHom_def, Category.assoc]
  erw [← whiskerLeft_comp_assoc, freeAtGenerator_lift, whiskerLeft_id, Category.id_comp]
  erw [convolutionUnit_evaluation]
  rw [← curry_pre_app, curry_uncurry]
  rfl

/-- endの射影は添字の射と、値域の後ろのブロックの射を対応させる。 -/
@[reassoc]
lemma internalHomProjection_map (F G : SymmetricSequence C) {x y : FiniteBijection}
    (f : x ⟶ y) (j : FiniteBijection) :
    ((ihom F).obj G).map f ≫ internalHomProjection F G y j =
      internalHomProjection F G x j ≫ (ihom (F.obj j)).map (G.map (j ◁ f)) :=
  (dayInternalHom F G).map_comp_π f j

/-- 各段の比較は後ろのブロックの置換作用と両立する。 -/
@[reassoc]
lemma freeInternalHomLevelIso_permutation (n m : ℕ) (X : C) (F : SymmetricSequence C)
    (σ : Equiv.Perm (Fin m)) :
    ((ihom ((freeAt n).obj X)).obj F).map (FiniteBijection.permutation m σ) ≫
        (freeInternalHomLevelIso n m X F).hom =
      (freeInternalHomLevelIso n m X F).hom ≫ (ihom X).map
        (F.map (FiniteBijection.sumMap (𝟙 (FiniteBijection.of n))
          (FiniteBijection.permutation m σ))) := by
  rw [freeInternalHomLevelIso_hom_projection]
  simp only [Category.assoc]
  rw [internalHomProjection_map_assoc]
  erw [← pre_comm_ihom_map]
  rfl

/-- 各添字を先頭n要素の追加でずらし、Xからの通常の内部Homを取る対称列。 -/
def shiftedInternalHom (n : ℕ) (X : C) (F : SymmetricSequence C) : SymmetricSequence C :=
  tensorLeft (FiniteBijection.of n) ⋙ toFunctorCategory.obj F ⋙ ihom X

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- ずらした内部Homの第m段は第n+m段への通常の内部Hom。 -/
lemma shiftedInternalHom_level (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    level (shiftedInternalHom n X F) m = (ihom X).obj (level F (n + m)) := rfl

/-- 各段の比較を、対称群作用を持つ対象の同型へ持ち上げる。 -/
def freeInternalHomLevelActionIso (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    levelAction ((ihom ((freeAt n).obj X)).obj F) m ≅
      levelAction (shiftedInternalHom n X F) m :=
  Action.mkIso (freeInternalHomLevelIso n m X F)
    (fun σ => freeInternalHomLevelIso_permutation n m X F σ)

end SerrePositivity.SymmetricSequence
