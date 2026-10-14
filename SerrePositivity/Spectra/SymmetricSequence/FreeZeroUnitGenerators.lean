module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroUnit
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolutionNaturality
public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # 自由零生成の単位比較と生成元の両立 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 単位比較の逆射はconvolutionの単位射を第0段の生成元へ送る。 -/
lemma freeZeroUnitIso_generator_inv :
    (convolutionUnitCan (C := C)).app ⟨⟨⟩⟩ ≫
        (freeZeroUnitIso (C := C)).inv.app (FiniteBijection.of 0) =
      freeAtGenerator 0 (𝟙_ C) := by
  unfold freeZeroUnitIso
  simp only [Iso.trans_inv, Category.assoc]
  change convolutionUnitCan.app ⟨⟨⟩⟩ ≫
    (λ_ ((𝟙_ (SymmetricSequence C)).obj (FiniteBijection.of 0))).inv ≫
      (freeZeroConvolutionLevelIso (𝟙_ C) (𝟙_ (SymmetricSequence C)) 0).inv ≫
        (ρ_ ((freeAt 0).obj (𝟙_ C))).hom.app (FiniteBijection.of 0) = _
  rw [← freeZeroConvolutionGenerator_eq_inv]
  unfold freeZeroConvolutionGenerator
  simp only [Category.assoc]
  erw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  erw [NatTrans.naturality]
  have hr := convolution_rightUnitor_generator ((freeAt 0).obj (𝟙_ C))
    (FiniteBijection.of 0)
  erw [reassoc_of% hr]
  erw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc]
  erw [← CategoryTheory.Functor.map_comp]
  erw [← indexRightUnitor_eq]
  erw [unitors_equal, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 単位比較の順射は第0段の生成元をconvolutionの単位射へ送る。 -/
@[reassoc]
lemma freeZeroUnitIso_generator_hom :
    freeAtGenerator 0 (𝟙_ C) ≫ (freeZeroUnitIso (C := C)).hom.app (FiniteBijection.of 0) =
      (convolutionUnitCan (C := C)).app ⟨⟨⟩⟩ := by
  apply (cancel_mono ((freeZeroUnitIso (C := C)).inv.app (FiniteBijection.of 0))).mp
  erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, freeZeroUnitIso_generator_inv]

end SerrePositivity.SymmetricSequence
