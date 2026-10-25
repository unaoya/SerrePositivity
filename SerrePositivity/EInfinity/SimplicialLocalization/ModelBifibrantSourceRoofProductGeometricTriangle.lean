module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductGeometricLeftHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact stableHomotopyRetarget (roofCornerEvaluationLeftHomotopy (modelBifibrantDKFrame X q)
    (modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b
    (modelBifibrantSourceRoofProductCommaCornerMap X Y q b))
    (modelBifibrantSourceRoofProductCommaCornerMap_diagram X Y q b) rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductGeometricRightHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex Y)) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact stableHomotopyRetarget (roofCornerEvaluationRightHomotopy (modelBifibrantDKFrame X q)
    (modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b
    (modelBifibrantSourceRoofProductCommaCornerMap X Y q b))
    (modelBifibrantSourceRoofProductCommaCornerMap_diagram X Y q b) rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductGeometricLeftCell :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (modelBifibrantSourceRoofProductGeometricLeftHomotopy X Y q b))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductGeometricRightCell :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (modelBifibrantSourceRoofProductGeometricRightHomotopy X Y q b))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometric_triangle :
    modelBifibrantSourceRoofProductGeometricLeftCell X Y q b ≫
      modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
        modelBifibrantSourceRoofProductGeometricRightCell X Y q b := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  simpa only [modelBifibrantSourceRoofProductGeometricLeftCell,
    modelBifibrantSourceRoofProductGeometricRightCell,
      modelBifibrantSourceRoofProductGeometricLeftHomotopy,
    modelBifibrantSourceRoofProductGeometricRightHomotopy,
      modelBifibrantSourceRoofProductActualIntervalCell,
    modelBifibrantSourceRoofProductCommaHomMap, modelBifibrantSourceRoofProductHomMap,
    modelBifibrantSourceRoofProductCommaCornerMap, modelBifibrantSourceRoofCornerEvaluation,
    Category.assoc, modelBifibrantObject, modelBifibrantHammockVertex,
      modelBifibrantSourceRoofDegreeObject,
    modelBifibrantDKFrame, modelBifibrantSourceRoofDegree, Functor.comp_obj,
    ULiftHom.up, ULiftHom.objUp, AsSmall.down, AsSmall.up,
    modelBifibrantRelativeCategory] using
    roofCornerEvaluation_triangle_retarget (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b
      (modelBifibrantSourceRoofProductCommaCornerMap X Y q b) _
      (modelBifibrantSourceRoofProductCommaCornerMap_diagram X Y q b)

end SerrePositivity.EInfinity.SimplicialLocalization
