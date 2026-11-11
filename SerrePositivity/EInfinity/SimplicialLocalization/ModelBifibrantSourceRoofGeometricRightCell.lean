module

public import SerrePositivity.EInfinity.FrameHom.NerveOverRightPrism
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofRightSlice
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle

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
open CategoryTheory Limits Opposite SSet MonoidalClosed
open SerrePositivity.EInfinity.FrameHom.FrameArrows
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometricRightHomotopy_h :
    (modelBifibrantSourceRoofProductGeometricRightHomotopy X Y q b).h =
      (modelBifibrantSourceRoofProductCommaRightHomotopy X Y q b).h := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  have h := nerveOverRightSliceMap_evaluation_h
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (modelBifibrantSourceRoofProductCommaRightOver X Y q b)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy (modelBifibrantHammockVertex Y))
    (modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
      roofCornerSourceSliceMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b)).h = _
  rw [modelBifibrantSourceRoofProductCommaRightSlice]
  exact h

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometricRightCell_eq :
    modelBifibrantSourceRoofProductGeometricRightCell X Y q b =
      modelBifibrantSourceRoofProductCommaRightCell X Y q b := by
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact congrArg (fun g => SSet.yonedaEquiv (curry g))
    (modelBifibrantSourceRoofProductGeometricRightHomotopy_h X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometric_triangle_right_standard :
    modelBifibrantSourceRoofProductGeometricLeftCell X Y q b ≫
      modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b :=
  (modelBifibrantSourceRoofProductGeometric_triangle X Y q b).trans
    (modelBifibrantSourceRoofProductGeometricRightCell_eq X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductActual_triangle_of_left_eq
    (hL : modelBifibrantSourceRoofProductGeometricLeftCell X Y q b =
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom) :
    (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b := by
  rw [← hL]
  exact modelBifibrantSourceRoofProductGeometric_triangle_right_standard X Y q b

end SerrePositivity.EInfinity.SimplicialLocalization
