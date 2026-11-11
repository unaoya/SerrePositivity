module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricRightCell

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
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open scoped Simplicial
open HomotopicalAlgebra SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometricLeftCell_eq :
    modelBifibrantSourceRoofProductGeometricLeftCell X Y q b =
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom := by
  let w := nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b)) ≫
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (modelBifibrantSourceRoofProductBaseHomotopy X Y q b) w
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (overTerminalHomotopy (modelBifibrantSourceRoofDegree X Y q b)
    (modelBifibrantSourceRoofProductCommaOver X Y q b)) w
  have h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
    exact congrArg (fun f => (hoFunctor.map
      ((ihom (nerve (modelBifibrantSourceRoofProductComma X Y q b))).map w)).toFunctor.map f)
      (modelBifibrantSourceRoofProductBaseHomotopy_hom_eq X Y q b)
  apply Arrow.mk_injective
  calc
    Arrow.mk (modelBifibrantSourceRoofProductGeometricLeftCell X Y q b) =
        Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      apply congrArg (fun g => SSet.yonedaEquiv (curry g))
      exact modelBifibrantSourceRoofProductGeometricLeftHomotopy_h_base X Y q b
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T)) := congrArg Arrow.mk h
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b))) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      apply congrArg (fun g => SSet.yonedaEquiv (curry g))
      exact modelBifibrantSourceRoofProductOverTerminalHomotopy_evaluation_h X Y q b
    _ = _ := congrArg Arrow.mk (modelBifibrantSourceRoofProductCommaEvaluationHomotopy_hom X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductActual_triangle :
    (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b :=
  modelBifibrantSourceRoofProductActual_triangle_of_left_eq X Y q b
    (modelBifibrantSourceRoofProductGeometricLeftCell_eq X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductActualIntervalCell_eq_comparison :
    modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
      modelBifibrantSourceRoofProductCommaComparisonCell X Y q b :=
  modelBifibrantSourceRoofProductCommaComparisonCell_unique X Y q b _
    (modelBifibrantSourceRoofProductActual_triangle X Y q b)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductHomMap_weak_of_reference_triangle
    (hR : (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b) :=
  modelBifibrantSourceRoofProductHomMap_weak_of_interval_triangles X Y q b r
    (modelBifibrantSourceRoofProductActual_triangle X Y q b) hR

include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal_of_reference_triangle
    (hR : ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
        modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b =
          modelBifibrantSourceRoofProductCommaRightCell X Y q b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) :=
  modelBifibrantSourceRoofMap_isLeftCofinal_of_interval_triangles X Y q r
    (fun b => modelBifibrantSourceRoofProductActual_triangle X Y q b) hR

end SerrePositivity.EInfinity.SimplicialLocalization
