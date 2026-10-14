module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolutionNaturality
public import SerrePositivity.Spectra.SymmetricSequence.DayAssociativityComparisons
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # 二つの零次自由生成を反復したconvolutionの各段の比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 二つの零次生成元から右結合したconvolutionへ入る標準射。 -/
def freeZeroPairConvolutionGenerator (X Y : C) (F : SymmetricSequence C) (q : ℕ) :
    (X ⊗ Y) ⊗ level F q ⟶ level ((freeAt 0).obj X ⊗ ((freeAt 0).obj Y ⊗ F)) q :=
  (α_ X Y (level F q)).hom ≫ X ◁ freeZeroConvolutionGenerator Y F q ≫
    freeZeroConvolutionGenerator X (((freeAt 0).obj Y) ⊗ F) q

/-- 反復した生成元を二つの各段の比較へ送ると通常の結合子になる。 -/
lemma freeZeroPairConvolutionGenerator_comparison (X Y : C) (F : SymmetricSequence C)
    (q : ℕ) :
    freeZeroPairConvolutionGenerator X Y F q ≫
        (((freeAt 0).obj X ◁ (freeZeroConvolutionNatIso Y).hom.app F) ≫
          (freeZeroConvolutionNatIso X).hom.app ((pointwiseTensorFunctor Y).obj F)).app
            (FiniteBijection.of q) = (α_ X Y (level F q)).hom := by
  have hn := freeZeroConvolutionGenerator_naturality (𝟙 X)
    ((freeZeroConvolutionNatIso Y).hom.app F) q
  erw [CategoryTheory.Functor.map_id] at hn
  simp only [id_tensorHom] at hn
  unfold freeZeroPairConvolutionGenerator
  simp only [Category.assoc]
  erw [NatTrans.comp_app, reassoc_of% hn]
  change (α_ X Y (level F q)).hom ≫ X ◁ freeZeroConvolutionGenerator Y F q ≫
    X ◁ (freeZeroConvolutionLevelIso Y F q).hom ≫
      freeZeroConvolutionGenerator X ((pointwiseTensorFunctor Y).obj F) q ≫
        (freeZeroConvolutionLevelIso X ((pointwiseTensorFunctor Y).obj F) q).hom = _
  erw [← whiskerLeft_comp_assoc, freeZeroConvolutionGenerator_comparison,
    whiskerLeft_id, Category.id_comp, freeZeroConvolutionGenerator_comparison,
    Category.comp_id]

/-- 空の二つのブロックの逆結合子は左単位子の左テンソルに一致する。 -/
lemma zero_zero_index_associator_inv (q : ℕ) :
    (α_ (FiniteBijection.of 0) (FiniteBijection.of 0) (FiniteBijection.of q)).inv =
      (FiniteBijection.of 0) ◁ (λ_ (FiniteBijection.of q)).hom := by
  apply (cancel_epi
    (α_ (FiniteBijection.of 0) (FiniteBijection.of 0) (FiniteBijection.of q)).hom).mp
  erw [Iso.hom_inv_id, CategoryTheory.MonoidalCategory.triangle]
  erw [← unitors_equal, FiniteBijection.leftUnitor_of_hom]
  simp only [eqToHom_refl]
  erw [id_whiskerRight]
  rfl

/-- 和次数零への比較を分け、convolutionの結合子を適用する射。 -/
def freeZeroConvolutionSplit (X Y : C) (F : SymmetricSequence C) :
    (freeAt 0).obj (X ⊗ Y) ⊗ F ⟶ (freeAt 0).obj X ⊗ ((freeAt 0).obj Y ⊗ F) :=
  (freePairConvolutionIso 0 0 X Y).inv ▷ F ≫
    (α_ ((freeAt 0).obj X) ((freeAt 0).obj Y) F).hom

omit [HasLimitsOfSize.{0, 0} C] in
/-- 和次数の比較と結合子は二つの零次生成元からの標準射を対応させる。 -/
lemma freeZeroConvolutionGenerator_split (X Y : C) (F : SymmetricSequence C) (q : ℕ) :
    freeZeroConvolutionGenerator (X ⊗ Y) F q ≫
        (freeZeroConvolutionSplit X Y F).app (FiniteBijection.of q) =
      freeZeroPairConvolutionGenerator X Y F q := by
  unfold freeZeroConvolutionGenerator freeZeroConvolutionSplit
    freeZeroPairConvolutionGenerator
  unfold freeZeroConvolutionGenerator
  simp only [whiskerLeft_comp, Category.assoc]
  erw [NatTrans.naturality, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [convolutionUnit_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    freePairConvolutionIso_generator_inv 0 0 X Y]
  unfold freePairConvolutionGenerator
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  have hc := convolution_associator_generator ((freeAt 0).obj X) ((freeAt 0).obj Y) F
    (FiniteBijection.of 0) (FiniteBijection.of 0) (FiniteBijection.of q)
  erw [reassoc_of% hc]
  have ha := CategoryTheory.MonoidalCategory.associator_naturality
    (freeAtGenerator 0 X) (freeAtGenerator 0 Y) (𝟙 (level F q))
  rw [tensorHom_id, tensorHom_id] at ha
  rw [tensorHom_def (freeAtGenerator 0 X) (freeAtGenerator 0 Y ▷ level F q)] at ha
  erw [reassoc_of% ha]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  erw [whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  have hu := (convolutionUnit ((freeAt 0).obj X) (((freeAt 0).obj Y) ⊗ F)).naturality
    (X := (FiniteBijection.of 0, (𝟙_ FiniteBijection) ⊗ FiniteBijection.of q))
    (Y := (FiniteBijection.of 0, FiniteBijection.of q))
    (𝟙 (FiniteBijection.of 0), (λ_ (FiniteBijection.of q)).hom)
  change ((((freeAt 0).obj X).map (𝟙 (FiniteBijection.of 0))) ▷
      ((((freeAt 0).obj Y) ⊗ F).obj ((𝟙_ FiniteBijection) ⊗ FiniteBijection.of q)) ≫
    ((freeAt 0).obj X).obj (FiniteBijection.of 0) ◁
      (((freeAt 0).obj Y) ⊗ F).map (λ_ (FiniteBijection.of q)).hom) ≫
      (convolutionUnit ((freeAt 0).obj X) (((freeAt 0).obj Y) ⊗ F)).app
        (FiniteBijection.of 0, FiniteBijection.of q) =
    (convolutionUnit ((freeAt 0).obj X) (((freeAt 0).obj Y) ⊗ F)).app
      (FiniteBijection.of 0, (𝟙_ FiniteBijection) ⊗ FiniteBijection.of q) ≫
        (((freeAt 0).obj X) ⊗ (((freeAt 0).obj Y) ⊗ F)).map
          (𝟙 (FiniteBijection.of 0) ⊗ₘ (λ_ (FiniteBijection.of q)).hom) at hu
  erw [CategoryTheory.Functor.map_id, id_whiskerRight, Category.id_comp, id_tensorHom] at hu
  erw [reassoc_of% hu]
  erw [← CategoryTheory.Functor.map_comp, ← indexAssociator_eq,
    zero_zero_index_associator_inv, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 二つの零次自由生成のconvolutionと各段の通常の結合の比較。 -/
def freeZeroConvolutionAssociatorIso (X Y : C) (F : SymmetricSequence C) :
    (pointwiseTensorFunctor (X ⊗ Y)).obj F ≅
      (pointwiseTensorFunctor X).obj ((pointwiseTensorFunctor Y).obj F) :=
  ((freeZeroConvolutionNatIso (X ⊗ Y)).app F).symm ≪≫
    (tensorRight F).mapIso (freePairConvolutionIso 0 0 X Y).symm ≪≫
      α_ ((freeAt 0).obj X) ((freeAt 0).obj Y) F ≪≫
        (tensorLeft ((freeAt 0).obj X)).mapIso ((freeZeroConvolutionNatIso Y).app F) ≪≫
          (freeZeroConvolutionNatIso X).app ((pointwiseTensorFunctor Y).obj F)

/-- 結同比較の順射をconvolutionの比較の合成として記述する。 -/
lemma freeZeroConvolutionAssociatorIso_hom (X Y : C) (F : SymmetricSequence C) :
    (freeZeroConvolutionAssociatorIso X Y F).hom =
      (freeZeroConvolutionNatIso (X ⊗ Y)).inv.app F ≫
        (freePairConvolutionIso 0 0 X Y).inv ▷ F ≫
          (α_ ((freeAt 0).obj X) ((freeAt 0).obj Y) F).hom ≫
            (freeAt 0).obj X ◁ (freeZeroConvolutionNatIso Y).hom.app F ≫
              (freeZeroConvolutionNatIso X).hom.app ((pointwiseTensorFunctor Y).obj F) := rfl

/-- 二つの零次自由生成を分けた結同比較の各段は通常の結合子。 -/
lemma freeZeroConvolutionAssociatorIso_level (X Y : C) (F : SymmetricSequence C) (q : ℕ) :
    (freeZeroConvolutionAssociatorIso X Y F).hom.app (FiniteBijection.of q) =
      (α_ X Y (level F q)).hom := by
  rw [freeZeroConvolutionAssociatorIso_hom]
  change (freeZeroConvolutionLevelIso (X ⊗ Y) F q).inv ≫
    ((freePairConvolutionIso 0 0 X Y).inv ▷ F).app (FiniteBijection.of q) ≫
      (α_ ((freeAt 0).obj X) ((freeAt 0).obj Y) F).hom.app (FiniteBijection.of q) ≫
        ((freeAt 0).obj X ◁ (freeZeroConvolutionNatIso Y).hom.app F).app
          (FiniteBijection.of q) ≫
            ((freeZeroConvolutionNatIso X).hom.app ((pointwiseTensorFunctor Y).obj F)).app
              (FiniteBijection.of q) = _
  rw [← freeZeroConvolutionGenerator_eq_inv]
  have hs := freeZeroConvolutionGenerator_split X Y F q
  change freeZeroConvolutionGenerator (X ⊗ Y) F q ≫
    ((freePairConvolutionIso 0 0 X Y).inv ▷ F).app (FiniteBijection.of q) ≫
      (α_ ((freeAt 0).obj X) ((freeAt 0).obj Y) F).hom.app (FiniteBijection.of q) = _ at hs
  erw [reassoc_of% hs]
  exact freeZeroPairConvolutionGenerator_comparison X Y F q

end SerrePositivity.SymmetricSequence
