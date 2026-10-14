module

public import SerrePositivity.Spectra.SymmetricSequence.DayAdjunction
public import SerrePositivity.Spectra.SymmetricSequence.FreePairConvolution

/-! # 自由対称列を原変数とする内部Homの各段

自由生成・convolution・基礎圏の閉構造の随伴により、和次数への内部Homと比較する。
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

/-- 和次数の自由生成の比較によるHom同値。 -/
def freePairHomEquiv (n m : ℕ) (X Y : C) (F : SymmetricSequence C) :
    (((freeAt n).obj X) ⊗ ((freeAt m).obj Y) ⟶ F) ≃
      ((freeAt (n + m)).obj (X ⊗ Y) ⟶ F) where
  toFun f := (freePairConvolutionIso n m X Y).inv ≫ f
  invFun f := (freePairConvolutionIso n m X Y).hom ≫ f
  left_inv f := by simp
  right_inv f := by simp

/-- 自由原変数の内部Homの第m段への射を、和次数への通常の内部Homへの射へ比較する。 -/
def freeInternalHomLevelEquiv (n m : ℕ) (X : C) (F : SymmetricSequence C) (Y : C) :
    (Y ⟶ level ((ihom ((freeAt n).obj X)).obj F) m) ≃
      (Y ⟶ (ihom X).obj (level F (n + m))) :=
  ((freeAtAdjunction m).homEquiv Y _).symm.trans <|
    ((ihom.adjunction ((freeAt n).obj X)).homEquiv _ F).symm.trans <|
      (freePairHomEquiv n m X Y F).trans <|
        ((freeAtAdjunction (n + m)).homEquiv (X ⊗ Y) F).trans
          ((ihom.adjunction X).homEquiv Y (level F (n + m)))

/-- Hom同値を各随伴の転置の合成として記述する。 -/
lemma freeInternalHomLevelEquiv_apply (n m : ℕ) (X : C) (F : SymmetricSequence C)
    {Y : C} (f : Y ⟶ level ((ihom ((freeAt n).obj X)).obj F) m) :
    freeInternalHomLevelEquiv n m X F Y f =
      curry ((freeAtAdjunction (n + m)).homEquiv (X ⊗ Y) F
        ((freePairConvolutionIso n m X Y).inv ≫
          uncurry (((freeAtAdjunction m).homEquiv Y _).symm f))) := rfl

omit [HasLimitsOfSize.{0, 0} C] in
/-- 和次数の比較の逆射は第二の生成対象の射に関して自然。 -/
@[reassoc]
lemma freePairConvolutionIso_inv_naturality_right (n m : ℕ) (X : C)
    {Y Z : C} (g : Y ⟶ Z) :
    (freePairConvolutionIso n m X Y).inv ≫ (freeAt n).obj X ◁ (freeAt m).map g =
      (freeAt (n + m)).map (X ◁ g) ≫ (freePairConvolutionIso n m X Z).inv := by
  apply (cancel_mono (freePairConvolutionIso n m X Z).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := freePairConvolutionIso_naturality n m (𝟙 X) g
  erw [CategoryTheory.Functor.map_id] at h
  simp only [id_tensorHom] at h
  erw [h, Iso.inv_hom_id_assoc]

/-- 各段のHom同値はパラメータ対象の射に関して自然。 -/
lemma freeInternalHomLevelEquiv_naturality (n m : ℕ) (X : C) (F : SymmetricSequence C)
    {Y Z : C} (g : Y ⟶ Z) (f : Z ⟶ level ((ihom ((freeAt n).obj X)).obj F) m) :
    freeInternalHomLevelEquiv n m X F Y (g ≫ f) =
      g ≫ freeInternalHomLevelEquiv n m X F Z f := by
  rw [freeInternalHomLevelEquiv_apply, freeInternalHomLevelEquiv_apply]
  rw [(freeAtAdjunction m).homEquiv_naturality_left_symm]
  rw [uncurry_natural_left]
  change curry ((freeAtAdjunction (n + m)).homEquiv (X ⊗ Y) F
    ((freePairConvolutionIso n m X Y).inv ≫
      (freeAt n).obj X ◁ (freeAt m).map g ≫ uncurry _)) = _
  rw [freePairConvolutionIso_inv_naturality_right_assoc,
    (freeAtAdjunction (n + m)).homEquiv_naturality_left, curry_natural_left]

/-- 各段のHom同値は値域の対称列の射に関して自然。 -/
lemma freeInternalHomLevelEquiv_naturality_right (n m : ℕ) (X : C)
    {F G : SymmetricSequence C} (g : F ⟶ G) {Y : C}
    (f : Y ⟶ level ((ihom ((freeAt n).obj X)).obj F) m) :
    freeInternalHomLevelEquiv n m X G Y
        (f ≫ ((ihom ((freeAt n).obj X)).map g).app (FiniteBijection.of m)) =
      freeInternalHomLevelEquiv n m X F Y f ≫
        (ihom X).map (g.app (FiniteBijection.of (n + m))) := by
  rw [freeInternalHomLevelEquiv_apply, freeInternalHomLevelEquiv_apply]
  change curry ((freeAtAdjunction (n + m)).homEquiv _ G
    ((freePairConvolutionIso n m X Y).inv ≫
      uncurry (((freeAtAdjunction m).homEquiv Y _).symm
        (f ≫ (evaluation m).map ((ihom ((freeAt n).obj X)).map g))))) = _
  have h := (freeAtAdjunction (C := C) m).homEquiv_naturality_right_symm f
    ((ihom ((freeAt n).obj X)).map g)
  erw [h, uncurry_natural_right]
  rw [← Category.assoc, (freeAtAdjunction (n + m)).homEquiv_naturality_right]
  exact curry_natural_right _ _

/-- 自由原変数の内部Homの第m段は、値域の第n+m段への通常の内部Homと同型。 -/
def freeInternalHomLevelIso (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    level ((ihom ((freeAt n).obj X)).obj F) m ≅ (ihom X).obj (level F (n + m)) where
  hom := freeInternalHomLevelEquiv n m X F _ (𝟙 _)
  inv := (freeInternalHomLevelEquiv n m X F _).symm (𝟙 _)
  hom_inv_id := by
    apply (freeInternalHomLevelEquiv n m X F _).injective
    rw [freeInternalHomLevelEquiv_naturality, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := freeInternalHomLevelEquiv_naturality n m X F
      ((freeInternalHomLevelEquiv n m X F _).symm (𝟙 _)) (𝟙 _)
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm

/-- 自由原変数の各段の比較は値域の対称列の射に関して自然。 -/
@[reassoc]
lemma freeInternalHomLevelIso_naturality (n m : ℕ) (X : C)
    {F G : SymmetricSequence C} (f : F ⟶ G) :
    ((ihom ((freeAt n).obj X)).map f).app (FiniteBijection.of m) ≫
        (freeInternalHomLevelIso n m X G).hom =
      (freeInternalHomLevelIso n m X F).hom ≫
        (ihom X).map (f.app (FiniteBijection.of (n + m))) := by
  have h := freeInternalHomLevelEquiv_naturality_right n m X f (𝟙 _)
  have h' := freeInternalHomLevelEquiv_naturality n m X G
    (((ihom ((freeAt n).obj X)).map f).app (FiniteBijection.of m)) (𝟙 _)
  simp only [Category.id_comp, Category.comp_id] at h h'
  exact h'.symm.trans h

end SerrePositivity.SymmetricSequence
