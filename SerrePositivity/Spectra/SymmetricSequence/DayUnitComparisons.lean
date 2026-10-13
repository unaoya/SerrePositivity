module

public import SerrePositivity.Spectra.SymmetricSequence.DayMonoidal

/-! # Day convolution の左右単位の比較

単位を含むconvolutionからの射は、単位対象とconvolutionの二段の標準射上で決まる。
登録済みDay構造の標準射・whisker・単位子を、具体的なKan拡張の射と比較する。
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

/-- 左単位を含むconvolutionからの射は、二段の標準射上の値で決まる。 -/
lemma convolution_left_unit_hom_ext (F G : SymmetricSequence C)
    (f g : convolution convolutionTensorUnit F ⟶ G)
    (h : ∀ y : FiniteBijection,
      (convolutionUnitCan.app ⟨⟨⟩⟩ ▷ F.obj y) ≫
        (convolutionUnit convolutionTensorUnit F).app (FiniteBijection.of 0, y) ≫
          f.app (FiniteBijection.sumObj (FiniteBijection.of 0) y) =
      (convolutionUnitCan.app ⟨⟨⟩⟩ ▷ F.obj y) ≫
        (convolutionUnit convolutionTensorUnit F).app (FiniteBijection.of 0, y) ≫
          g.app (FiniteBijection.sumObj (FiniteBijection.of 0) y)) : f = g := by
  let hP := (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
    (convolutionTensorUnit (C := C)) convolutionUnitCan (toFunctorCategory.obj F)
    (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (FiniteBijection.of 0)) (Functor.fromPUnit.{0} (𝟙_ C))))
  let _ : (externalProduct (convolutionTensorUnit (C := C))
      (toFunctorCategory.obj F)).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft (convolutionTensorUnit (C := C))
        convolutionUnitCan (toFunctorCategory.obj F)) := hP.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _ (convolutionUnit convolutionTensorUnit F)
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft (convolutionTensorUnit (C := C))
      convolutionUnitCan (toFunctorCategory.obj F))
  ext ⟨p, y⟩
  have hp : p = ⟨⟨⟩⟩ := Subsingleton.elim _ _
  subst p
  dsimp [ExternalProduct.extensionUnitLeft]
  simpa only [whiskerLeft_id, Category.comp_id, toFunctorCategory,
    FiniteBijection.sumFunctor] using h y

omit [SymmetricCategory C] in
/-- 右単位を含むconvolutionからの射は、二段の標準射上の値で決まる。 -/
lemma convolution_right_unit_hom_ext (F G : SymmetricSequence C)
    (f g : convolution F convolutionTensorUnit ⟶ G)
    (h : ∀ y : FiniteBijection,
      (F.obj y ◁ convolutionUnitCan.app ⟨⟨⟩⟩) ≫
        (convolutionUnit F convolutionTensorUnit).app (y, FiniteBijection.of 0) ≫
          f.app (FiniteBijection.sumObj y (FiniteBijection.of 0)) =
      (F.obj y ◁ convolutionUnitCan.app ⟨⟨⟩⟩) ≫
        (convolutionUnit F convolutionTensorUnit).app (y, FiniteBijection.of 0) ≫
          g.app (FiniteBijection.sumObj y (FiniteBijection.of 0))) : f = g := by
  let hP := (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight
    (convolutionTensorUnit (C := C)) convolutionUnitCan (toFunctorCategory.obj F)
    (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (FiniteBijection.of 0)) (Functor.fromPUnit.{0} (𝟙_ C))))
  let _ : (externalProduct (toFunctorCategory.obj F)
      (convolutionTensorUnit (C := C))).IsLeftKanExtension
      (ExternalProduct.extensionUnitRight (convolutionTensorUnit (C := C))
        convolutionUnitCan (toFunctorCategory.obj F)) := hP.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _ (convolutionUnit F convolutionTensorUnit)
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitRight (convolutionTensorUnit (C := C))
      convolutionUnitCan (toFunctorCategory.obj F))
  ext ⟨y, p⟩
  have hp : p = ⟨⟨⟩⟩ := Subsingleton.elim _ _
  subst p
  dsimp [ExternalProduct.extensionUnitRight]
  simpa only [id_whiskerRight, Category.id_comp, toFunctorCategory,
    FiniteBijection.sumFunctor] using h y


/-- 登録済みDay構造の埋め込みは、既存の関手圏への入口。 -/
lemma lawfulEmbedding_eq :
    LawfulDayConvolutionMonoidalCategoryStruct.ι FiniteBijection C (SymmetricSequence C) =
      toFunctorCategory := rfl

/-- 登録済みDay構造の標準射の成分は、具体的なconvolutionの標準射。 -/
lemma lawfulConvolutionExtensionUnit_app (F G : SymmetricSequence C) (x y : FiniteBijection) :
    (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
        FiniteBijection C F G).app (x, y) = (convolutionUnit F G).app (x, y) := by
  simp only [LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit,
    InducedLawfulDayConvolutionMonoidalCategoryStructCore.convolutionUnitApp_eq,
    DayConvolution.unit, InducedLawfulDayConvolutionMonoidalCategoryStructCore.ι,
    toFunctorCategory]
  erw [Category.comp_id]

/-- 登録済みDay構造の単位の標準射は、空集合からのKan拡張の標準射。 -/
lemma lawfulUnitUnit_eq :
    LawfulDayConvolutionMonoidalCategoryStruct.unitUnit FiniteBijection C (SymmetricSequence C) =
      (convolutionUnitCan (C := C)).app ⟨⟨⟩⟩ := rfl

/-- 添字圏のテンソル積は直和。 -/
lemma indexTensor_eq_sum (x y : FiniteBijection) : x ⊗ y = FiniteBijection.sumObj x y := rfl
/-- 添字圏の単位は空集合。 -/
lemma indexUnit_eq_zero : 𝟙_ FiniteBijection = FiniteBijection.of 0 := rfl
/-- 添字圏の左単位子は直和の左単位同型。 -/
lemma indexLeftUnitor_eq (y : FiniteBijection) : (λ_ y) = FiniteBijection.sumLeftUnitor y := rfl
/-- 添字圏の右単位子は直和の右単位同型。 -/
lemma indexRightUnitor_eq (y : FiniteBijection) : (ρ_ y) = FiniteBijection.sumRightUnitor y := rfl

/-- 右whiskerの成分は、convolutionの標準射上で計算できる。 -/
@[reassoc] lemma convolutionUnit_whiskerRight {F F' : SymmetricSequence C}
    (η : F ⟶ F') (G : SymmetricSequence C) (x y : FiniteBijection) :
    (convolutionUnit F G).app (x, y) ≫ (η ▷ G).app (FiniteBijection.sumObj x y) =
      (η.app x ▷ G.obj y) ≫ (convolutionUnit F' G).app (x, y) :=
by
  have h :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      (D := SymmetricSequence C) FiniteBijection C η G x y
  simpa only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq,
    lawfulUnitUnit_eq, toFunctorCategory, indexTensor_eq_sum, indexUnit_eq_zero,
    indexLeftUnitor_eq, indexRightUnitor_eq, tensorUnit_eq_convolutionTensorUnit] using h

/-- 左whiskerの成分は、convolutionの標準射上で計算できる。 -/
@[reassoc] lemma convolutionUnit_whiskerLeft (F : SymmetricSequence C)
    {G G' : SymmetricSequence C} (η : G ⟶ G') (x y : FiniteBijection) :
    (convolutionUnit F G).app (x, y) ≫ (F ◁ η).app (FiniteBijection.sumObj x y) =
      (F.obj x ◁ η.app y) ≫ (convolutionUnit F G').app (x, y) :=
by
  have h :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      (D := SymmetricSequence C) C F η x y
  simpa only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq,
    lawfulUnitUnit_eq, toFunctorCategory, indexTensor_eq_sum, indexUnit_eq_zero,
    indexLeftUnitor_eq, indexRightUnitor_eq, tensorUnit_eq_convolutionTensorUnit] using h

/-- 登録済み左単位子の標準射上の比較。 -/
lemma convolution_leftUnitor_generator (F : SymmetricSequence C) (y : FiniteBijection) :
    (convolutionUnitCan.app ⟨⟨⟩⟩ ▷ F.obj y) ≫
        (convolutionUnit convolutionTensorUnit F).app (FiniteBijection.of 0, y) ≫
        (λ_ F).hom.app (FiniteBijection.sumObj (FiniteBijection.of 0) y) =
      (λ_ (F.obj y)).hom ≫ F.map (FiniteBijection.sumLeftUnitor y).inv :=
by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
    (D := SymmetricSequence C) C F y
  simpa only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq,
    lawfulUnitUnit_eq, toFunctorCategory, indexTensor_eq_sum, indexUnit_eq_zero,
    indexLeftUnitor_eq, indexRightUnitor_eq, tensorUnit_eq_convolutionTensorUnit] using h

/-- 登録済み右単位子の標準射上の比較。 -/
lemma convolution_rightUnitor_generator (F : SymmetricSequence C) (y : FiniteBijection) :
    (F.obj y ◁ convolutionUnitCan.app ⟨⟨⟩⟩) ≫
        (convolutionUnit F convolutionTensorUnit).app (y, FiniteBijection.of 0) ≫
        (ρ_ F).hom.app (FiniteBijection.sumObj y (FiniteBijection.of 0)) =
      (ρ_ (F.obj y)).hom ≫ F.map (FiniteBijection.sumRightUnitor y).inv :=
by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
    (D := SymmetricSequence C) C F y
  simpa only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq,
    lawfulUnitUnit_eq, toFunctorCategory, indexTensor_eq_sum, indexUnit_eq_zero,
    indexLeftUnitor_eq, indexRightUnitor_eq, tensorUnit_eq_convolutionTensorUnit] using h

end SerrePositivity.SymmetricSequence
