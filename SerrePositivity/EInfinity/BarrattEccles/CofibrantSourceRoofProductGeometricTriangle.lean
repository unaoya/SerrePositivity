module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCornerProjection
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductIntervalCriterion
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle

/-!
# 元の comma 全図式上の実評価の幾何的三角形

概要：同じ実 ProductHomMap の区間族と二つの実円柱を全関手圏で合成する。
方針：実 corner の一般三角形を元の comma 始域図式へ厳密に輸送する。
規約：標準自然変換の左右の脚との同定は別工程であり、ここでは仮定しない。
使われ方：実射側 hA の標準脚との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductGeometricLeftHomotopy : SSet.Homotopy
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (roofCornerEvaluationLeftHomotopy (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
    (cofibrantSourceRoofProductCommaCornerMap A X Y b))
    (cofibrantSourceRoofProductCommaCornerMap_diagram A X Y b) rfl

def cofibrantSourceRoofProductGeometricRightHomotopy : SSet.Homotopy
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (roofCornerEvaluationRightHomotopy (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
    (cofibrantSourceRoofProductCommaCornerMap A X Y b))
    (cofibrantSourceRoofProductCommaCornerMap_diagram A X Y b) rfl

def cofibrantSourceRoofProductGeometricLeftCell :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (cofibrantSourceRoofProductGeometricLeftHomotopy A X Y b))

def cofibrantSourceRoofProductGeometricRightCell :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (cofibrantSourceRoofProductGeometricRightHomotopy A X Y b))

lemma cofibrantSourceRoofProductGeometric_triangle :
    cofibrantSourceRoofProductGeometricLeftCell A X Y b ≫
      cofibrantSourceRoofProductActualIntervalCell A X Y b =
        cofibrantSourceRoofProductGeometricRightCell A X Y b := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  simpa only [cofibrantSourceRoofProductGeometricLeftCell,
    cofibrantSourceRoofProductGeometricRightCell, cofibrantSourceRoofProductGeometricLeftHomotopy,
    cofibrantSourceRoofProductGeometricRightHomotopy, cofibrantSourceRoofProductActualIntervalCell,
    cofibrantSourceRoofProductCommaHomMap, cofibrantSourceRoofProductHomMap,
    cofibrantSourceRoofProductCommaCornerMap, cofibrantSourceRoofCornerEvaluation,
    Category.assoc, cofibrantHammockVertex, cofibrantSourceRoofDegreeAlgebra,
    cofibrantDKSourceFrame, cofibrantSourceRoofDegree, Functor.comp_obj,
    ULiftHom.up, ULiftHom.objUp, AsSmall.down] using
    roofCornerEvaluation_triangle_retarget (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
      (cofibrantSourceRoofProductCommaCornerMap A X Y b) _
      (cofibrantSourceRoofProductCommaCornerMap_diagram A X Y b)

end SerrePositivity.EInfinity.BarrattEccles
