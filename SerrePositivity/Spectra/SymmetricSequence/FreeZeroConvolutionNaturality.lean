module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroEvaluationGenerators

/-! # 生成次数零のconvolutionの比較の両変数の自然性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open LawfulDayConvolutionMonoidalCategoryStruct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

omit [HasLimitsOfSize.{0, 0} C] in
/-- 第0段の生成元からの標準射は、生成対象と値域対称列の射に関して自然。 -/
@[reassoc]
lemma freeZeroConvolutionGenerator_naturality {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) (q : ℕ) :
    freeZeroConvolutionGenerator X F q ≫ (((freeAt 0).map f) ⊗ₘ g).app (FiniteBijection.of q) =
      (f ⊗ₘ g.app (FiniteBijection.of q)) ≫ freeZeroConvolutionGenerator Y G q := by
  have hn := convolutionExtensionUnit_comp_ι_map_tensorHom_app FiniteBijection C
    ((freeAt 0).map f) g (FiniteBijection.of 0) (FiniteBijection.of q)
  simp only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq, toFunctorCategory,
    indexTensor_eq_sum] at hn
  have hf : freeAtGenerator 0 X ≫ ((freeAt 0).map f).app (FiniteBijection.of 0) =
      f ≫ freeAtGenerator 0 Y := freeAtInclusion_map_input 0 f (𝟙 _)
  unfold freeZeroConvolutionGenerator
  simp only [Category.assoc]
  erw [NatTrans.naturality, reassoc_of% hn]
  rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, hf, Category.id_comp]
  have ht : (f ⊗ₘ g.app (FiniteBijection.of q)) ≫ freeAtGenerator 0 Y ▷ level G q =
      (f ≫ freeAtGenerator 0 Y) ⊗ₘ g.app (FiniteBijection.of q) := by
    erw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  erw [← ht]
  simp only [Category.assoc]

/-- 各段の逆比較は両変数の射と両立する。 -/
@[reassoc]
lemma freeZeroConvolutionLevelIso_inv_naturality {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) (q : ℕ) :
    (freeZeroConvolutionLevelIso X F q).inv ≫
        (((freeAt 0).map f) ⊗ₘ g).app (FiniteBijection.of q) =
      (f ⊗ₘ g.app (FiniteBijection.of q)) ≫ (freeZeroConvolutionLevelIso Y G q).inv := by
  rw [← freeZeroConvolutionGenerator_eq_inv, ← freeZeroConvolutionGenerator_eq_inv]
  exact freeZeroConvolutionGenerator_naturality f g q

/-- 各段の順比較も両変数の射と両立する。 -/
@[reassoc]
lemma freeZeroConvolutionLevelIso_naturality {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) (q : ℕ) :
    (((freeAt 0).map f) ⊗ₘ g).app (FiniteBijection.of q) ≫
        (freeZeroConvolutionLevelIso Y G q).hom =
      (freeZeroConvolutionLevelIso X F q).hom ≫ (f ⊗ₘ g.app (FiniteBijection.of q)) := by
  apply (cancel_epi (freeZeroConvolutionLevelIso X F q).inv).mp
  erw [freeZeroConvolutionLevelIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

end SerrePositivity.SymmetricSequence
