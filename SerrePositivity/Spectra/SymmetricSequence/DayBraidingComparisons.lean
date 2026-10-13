module

public import SerrePositivity.Spectra.SymmetricSequence.DaySymmetry
public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons

/-! # Day convolution のbraidingと可換性の帰着

登録済みconvolutionのbraidingを、標準射・各段のbraiding・添字圏のブロック交換へ展開する。
乗法の可換性を標準射上の等式へ帰着する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

attribute [local instance] LawfulDayConvolutionMonoidalCategoryStruct.convolution
/-- 添字圏のbraidingは二ブロック全体の交換。 -/
lemma indexBraiding_eq (x y : FiniteBijection) : β_ x y = FiniteBijection.sumSymmetry x y := rfl
/-- convolutionのbraidingを標準射上で計算する。 -/
@[reassoc] lemma convolution_braiding_generator (F G : SymmetricSequence C)
    (x y : FiniteBijection) :
    (convolutionUnit F G).app (x, y) ≫
        (β_ F G).hom.app (FiniteBijection.sumObj x y) =
      (β_ (F.obj x) (G.obj y)).hom ≫
        (convolutionUnit G F).app (y, x) ≫
        (convolution G F).map (FiniteBijection.sumSymmetry y x).hom := by
  have h := DayConvolution.unit_app_braiding_hom_app (dayEmbedding.obj F)
    (dayEmbedding.obj G) x y
  rw [← dayEmbedding_map_braiding] at h
  simpa only [DayConvolution.unit, LawfulDayConvolutionMonoidalCategoryStruct.convolution,
    lawfulConvolutionExtensionUnit_app, dayEmbedding, lawfulEmbedding_eq, toFunctorCategory,
    indexTensor_eq_sum, indexBraiding_eq, DayConvolution.convolution,
    tensorObj_eq_convolution, BraidedCategory.braiding, convolutionSymmetricCategory] using h

/-- 乗法の可換性は、標準射上のブロック交換の等式と同値。 -/
lemma convolution_commutativity_iff (F : SymmetricSequence C)
    (μ : convolution F F ⟶ F) :
    (β_ F F).hom ≫ μ = μ ↔
      ∀ x y : FiniteBijection,
        (β_ (F.obj x) (F.obj y)).hom ≫ (convolutionUnit F F).app (y, x) ≫
          μ.app (FiniteBijection.sumObj y x) ≫ F.map (FiniteBijection.sumSymmetry y x).hom =
        (convolutionUnit F F).app (x, y) ≫ μ.app (FiniteBijection.sumObj x y) := by
  constructor
  · intro h x y
    have hh := congrArg (fun η ↦ (convolutionUnit F F).app (x, y) ≫
      η.app (FiniteBijection.sumObj x y)) h
    erw [NatTrans.comp_app] at hh
    erw [convolution_braiding_generator_assoc] at hh
    erw [NatTrans.naturality μ] at hh
    exact hh
  · intro h
    apply Functor.hom_ext_of_isLeftKanExtension _ (convolutionUnit F F)
    ext ⟨x, y⟩
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    erw [convolution_braiding_generator_assoc]
    erw [NatTrans.naturality μ]
    exact h x y

end SerrePositivity.SymmetricSequence
