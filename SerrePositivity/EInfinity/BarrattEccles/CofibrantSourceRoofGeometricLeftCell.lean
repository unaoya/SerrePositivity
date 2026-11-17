module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofEvaluationHomotopy
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofGeometricRightCell

/-!
# 元の実屋根評価の左脚と標準評価の同定、および全三角形 hA

概要：元の全関手圏で左脚を標準評価へ同定し、同じ実区間族の三角形を閉じる。
方針：Over n の全底円柱の一意性を同じ元の q で送り、標準右脚の等式に接続する。
規約：任意可換環・全パラメータ・同じ実 ProductHomMap を保つ。
使われ方：弱な基準射側の全三角形 hR と合わせた実屋根 cofinality。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet MonoidalClosed
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductGeometricLeftCell_eq :
    cofibrantSourceRoofProductGeometricLeftCell A X Y b =
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom := by
  let w := nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b)) ≫
    nerveMap (cofibrantDKSourceFrame A X) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (cofibrantSourceRoofProductBaseHomotopy A X Y b) w
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.overTerminalHomotopy (cofibrantSourceRoofDegree A X Y b)
    (cofibrantSourceRoofProductCommaOver A X Y b)) w
  have h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
    exact congrArg (fun f => (hoFunctor.map
      ((ihom (nerve (cofibrantSourceRoofProductComma A X Y b))).map w)).toFunctor.map f)
      (cofibrantSourceRoofProductBaseHomotopy_hom_eq A X Y b)
  apply Arrow.mk_injective
  calc
    Arrow.mk (cofibrantSourceRoofProductGeometricLeftCell A X Y b) =
        Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      apply congrArg (fun g => SSet.yonedaEquiv (curry g))
      exact cofibrantSourceRoofProductGeometricLeftHomotopy_h_base A X Y b
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T)) := congrArg Arrow.mk h
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b))) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      apply congrArg (fun g => SSet.yonedaEquiv (curry g))
      exact cofibrantSourceRoofProductOverTerminalHomotopy_evaluation_h A X Y b
    _ = _ := congrArg Arrow.mk (cofibrantSourceRoofProductCommaEvaluationHomotopy_hom A X Y b)

lemma cofibrantSourceRoofProductActual_triangle :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductActualIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b :=
  cofibrantSourceRoofProductActual_triangle_of_left_eq A X Y b
    (cofibrantSourceRoofProductGeometricLeftCell_eq A X Y b)

lemma cofibrantSourceRoofProductActualIntervalCell_eq_comparison :
    cofibrantSourceRoofProductActualIntervalCell A X Y b =
      cofibrantSourceRoofProductCommaComparisonCell A X Y b :=
  cofibrantSourceRoofProductCommaComparisonCell_unique A X Y b _
    (cofibrantSourceRoofProductActual_triangle A X Y b)

lemma cofibrantSourceRoofProductHomMap_weak_of_reference_triangle
    (hR : (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b) :=
  cofibrantSourceRoofProductHomMap_weak_of_interval_triangles A X Y b
    (cofibrantSourceRoofProductActual_triangle A X Y b) hR

lemma cofibrantSourceRoofMap_isLeftCofinal_of_reference_triangle
    (hR : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
        cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
          cofibrantSourceRoofProductCommaRightCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_interval_triangles A X Y
    (fun b => cofibrantSourceRoofProductActual_triangle A X Y b) hR

end SerrePositivity.EInfinity.BarrattEccles
