module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeActionUnitSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeActionReflectsEdgeClass

/-!
概要：元の標準単位の正方形から、元の指定頂点辺と同じ全空間 Kan 辺の類を同定する。
方針：指定辺の全余錐作用の合成式を供給し、単位三角形の比較と余極限同値で反映する。
規約：指定辺・変換・全 Kan 像を保持し、底の quasicategory 性を要求しない。
使われ方：実際の前層余極限の共役された各脚を、標準評価 Kan 脚へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory

/-- 元の二つの標準単位との可換式を満たす指定頂点辺は、同じ Kan 辺と同じ類。 -/
lemma totalKanNativeEdge_homMk_of_unit_square {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
    (h : homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone G) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex G))).toTruncated =
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F))).toTruncated ≫
          homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := (SSet.uliftFunctor.{u + 1, u}).obj B) e.toTruncated)) :
    homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t)).toTruncated =
      homMk e.toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.totalKanNativeEdge_homMk_of_coconeIso F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t) e
  have H := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanNativeCoconeIsoOfNativeUnitHomClass F G t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeEdgeAction (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeEdgeAction_vertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) e)
    (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeEdgeAction_unit_square (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) e).symm)
  exact H

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
