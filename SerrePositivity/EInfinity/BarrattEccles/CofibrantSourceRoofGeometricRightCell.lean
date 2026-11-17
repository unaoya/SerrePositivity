module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveOverRightPrism
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofRightSlice
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductGeometricTriangle

/-!
# 実評価の幾何的右脚は元の RightLeg の全円柱

概要：元の comma 全図式上で実評価の右脚と標準右脚を同定する。
方針：同じ qY slice の全 Over 表示と通常余錐の全 prism を接続する。
規約：全円柱の等式から全関手圏の射を同定する。
使われ方：実射側の全三角形 hA の右辺の標準化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet MonoidalClosed
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductGeometricRightHomotopy_h :
    (cofibrantSourceRoofProductGeometricRightHomotopy A X Y b).h =
      (cofibrantSourceRoofProductCommaRightHomotopy A X Y b).h := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.nerveOverRightSliceMap_evaluation_h
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (cofibrantSourceRoofProductCommaRightOver A X Y b)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy (cofibrantHammockVertex A Y))
    (cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b)).h = _
  rw [cofibrantSourceRoofProductCommaRightSlice]
  exact h

lemma cofibrantSourceRoofProductGeometricRightCell_eq :
    cofibrantSourceRoofProductGeometricRightCell A X Y b =
      cofibrantSourceRoofProductCommaRightCell A X Y b := by
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact congrArg (fun g => SSet.yonedaEquiv (curry g))
    (cofibrantSourceRoofProductGeometricRightHomotopy_h A X Y b)

lemma cofibrantSourceRoofProductGeometric_triangle_right_standard :
    cofibrantSourceRoofProductGeometricLeftCell A X Y b ≫
      cofibrantSourceRoofProductActualIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b :=
  (cofibrantSourceRoofProductGeometric_triangle A X Y b).trans
    (cofibrantSourceRoofProductGeometricRightCell_eq A X Y b)

lemma cofibrantSourceRoofProductActual_triangle_of_left_eq
    (hL : cofibrantSourceRoofProductGeometricLeftCell A X Y b =
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom) :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductActualIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b := by
  rw [← hL]
  exact cofibrantSourceRoofProductGeometric_triangle_right_standard A X Y b

end SerrePositivity.EInfinity.BarrattEccles
