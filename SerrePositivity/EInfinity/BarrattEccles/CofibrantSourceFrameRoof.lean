module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameElements
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameRightKan
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSource

/-!
# 元の sourceFrameHom の全単体から実 hammock の屋根比較への写像

概要：元の全単体を DK frame の固定終域の矢へ送り、同じ q の実屋根比較を適用する。
方針：元の要素圏の同値・native slice 引き戻しの同型・元の屋根写像を合成する。
規約：元の代数射・全作用素・指定終域と次数射影を保持する。
使われ方：実右 Kan 比較の left cofinality の核心となる元の屋根写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantSourceFrameRoofMap : nerve (sourceFrameElementCategory A X Y) ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)))
      (nerveMap (cofibrantDKSourceFrame A X) ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) :=
  (sourceFrameElementsDKNerveIso A X Y).hom ≫
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))

lemma cofibrantSourceFrameRoofMap_degree :
    cofibrantSourceFrameRoofMap A X Y ≫ pullback.snd _ _ =
      sourceFrameElementDegreeNerve A X Y := by
  rw [cofibrantSourceFrameRoofMap, Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap_degree]
  rfl

lemma cofibrantSourceFrameRoofMap_isLeftCofinal_iff_raw :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (nerveMap (cofibrantDKSourceFrame A X))
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)))) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_isIso (sourceFrameElementsDKNerveIso A X Y).hom
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))) :=
    ⟨hi.cancel_left, hi.comp⟩
  exact h.trans (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap_isLeftCofinal_iff_raw _ _ _)

end SerrePositivity.EInfinity.BarrattEccles
