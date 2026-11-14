module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TwistedArrowPointedEdgeCospan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TwistedArrowEdgeLifts

/-!
概要：二つの元の pointed 辺の底は、元の Yoneda 評価辺と反変辺そのもの。
方針：同じ全体の復元射の射影式を、元の二つの一単体に適用する。
規約：元の全辺の作用を厳密に照合し、Hom 類だけの一致へ弱めない。
使われ方：元の二方向の恒等点輸送を、同じ pointed 終点へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 始点側の元の pointed 辺の底は、元の Yoneda 射を始点で評価した同じ辺。 -/
lemma twistedArrowPointedSourceEdge_projection {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedSourceEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (SSet.opObjEquiv.symm
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))).app
            (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedSourceEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.yonedaInfinityMap_evaluate_sourceRestriction]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))).app
        (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) := by
    have h := congrArg (fun g ↦ SSet.yonedaEquiv g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdge_projection f)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have h := congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay_projection C)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C).app _
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C).app _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f))) at h
  rw [hp] at h
  exact h

/-- 終点側の元の pointed 辺の底は、同じ表現可能前層に元の反転辺を入れた辺。 -/
lemma twistedArrowPointedTargetEdge_projection {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedTargetEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋1⦌)
          (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedTargetEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_eq_targetRestriction]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app
        (Opposite.op ⦋1⦌) (SSet.opObjEquiv.symm (SSet.yonedaEquiv f)) := by
    have h := congrArg (fun g ↦ SSet.yonedaEquiv g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdge_projection f)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowOppositeEdge]
      using h
  have h := congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay_projection C)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C).app _
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C).app _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f))) at h
  rw [hp] at h
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
