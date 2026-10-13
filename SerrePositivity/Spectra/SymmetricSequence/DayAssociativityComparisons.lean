module

public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons

/-! # 三重 convolution の普遍性と結合子

二段の左Kan拡張により、三重convolutionからの射を標準射上で比較する。
登録済みDay構造の結合子の計算を、具体的なconvolutionへ接続する。
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

/-- 三重convolutionからの射は、二段の標準射上の値で決まる。 -/
lemma convolution_triple_hom_ext (F G H K : SymmetricSequence C)
    (f g : convolution (convolution F G) H ⟶ K)
    (h : ∀ x y z : FiniteBijection,
      ((convolutionUnit F G).app (x, y) ▷ H.obj z) ≫
        (convolutionUnit (convolution F G) H).app (FiniteBijection.sumObj x y, z) ≫
          f.app (FiniteBijection.sumObj (FiniteBijection.sumObj x y) z) =
      ((convolutionUnit F G).app (x, y) ▷ H.obj z) ≫
        (convolutionUnit (convolution F G) H).app (FiniteBijection.sumObj x y, z) ≫
          g.app (FiniteBijection.sumObj (FiniteBijection.sumObj x y) z)) : f = g := by
  let hP := ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
    (toFunctorCategory.obj (convolution F G)) (convolutionUnit F G) (toFunctorCategory.obj H)
    (convolutionIsPointwise F G)
  let _ : (externalProduct (toFunctorCategory.obj (convolution F G))
      (toFunctorCategory.obj H)).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft (toFunctorCategory.obj (convolution F G))
        (convolutionUnit F G) (toFunctorCategory.obj H)) := hP.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _ (convolutionUnit (convolution F G) H)
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft (toFunctorCategory.obj (convolution F G))
      (convolutionUnit F G) (toFunctorCategory.obj H))
  ext ⟨⟨x, y⟩, z⟩
  dsimp [ExternalProduct.extensionUnitLeft]
  simpa only [whiskerLeft_id, Category.comp_id, toFunctorCategory,
    FiniteBijection.sumFunctor] using h x y z

/-- 添字圏の結合子は直和の結合同型。 -/
lemma indexAssociator_eq (x y z : FiniteBijection) :
    α_ x y z = FiniteBijection.sumAssociator x y z := rfl

/-- 登録済みconvolutionの結合子の標準射上の計算。 -/
@[reassoc] lemma convolution_associator_generator (F G H : SymmetricSequence C)
    (x y z : FiniteBijection) :
    ((convolutionUnit F G).app (x, y) ▷ H.obj z) ≫
        (convolutionUnit (convolution F G) H).app (FiniteBijection.sumObj x y, z) ≫
        (α_ F G H).hom.app (FiniteBijection.sumObj (FiniteBijection.sumObj x y) z) =
      (α_ (F.obj x) (G.obj y) (H.obj z)).hom ≫
        (F.obj x ◁ (convolutionUnit G H).app (y, z)) ≫
        (convolutionUnit F (convolution G H)).app (x, FiniteBijection.sumObj y z) ≫
        (convolution F (convolution G H)).map (FiniteBijection.sumAssociator x y z).inv := by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
    (D := SymmetricSequence C) C F G H x y z
  simpa only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq, toFunctorCategory,
    indexTensor_eq_sum, indexAssociator_eq, tensorObj_eq_convolution] using h

end SerrePositivity.SymmetricSequence
