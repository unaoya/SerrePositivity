module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TwistedArrowEdgeCospan
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.PointedIdentity

/-!
概要：元の Tw の二辺を、同じ Yoneda 恒等点から同じ pointed 終点への二辺へ送る。
方針：一つの全体の復元射と、同じ恒等点の既存の厳密な一致を使う。
規約：端点を別に選び直さず、全体の射による同じ二つの辺を保持する。
使われ方：Yoneda の元の脚の恒等点像と、反変側の恒等点輸送の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 全体の同じ表示は、元の定値 Tw 恒等点を元の Yoneda 恒等点へ厳密に送る。 -/
lemma twistedArrowPointedDisplay_identity {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋0⦌) (ULift.up (SSet.const x)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity x).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.canonicalYonedaPointedIdentity_eq_sourceDisplay]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋0⦌) (ULift.up (SSet.const x)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋0⦌)
      (ULift.up ((pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion x)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity x)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity_fst]

/-- 元の辺の頂点を同じ全体の復元射で送った、二辺に共通する pointed 終点。 -/
def twistedArrowPointedEdgeVertex {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowEdgeVertex f))

/-- 元の始点の同じ Yoneda 恒等点から、同じ pointed 終点への実際の辺。 -/
def twistedArrowPointedSourceEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))).val
      (twistedArrowPointedEdgeVertex f) := by
  let e : SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C))
      (ULift.up (SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowEdgeVertex f)) :=
    ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f),
      congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex_src f),
      congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex_tgt f)⟩
  have h := e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C)
  exact ⟨h.edge, h.src_eq.trans (twistedArrowPointedDisplay_identity _), h.tgt_eq⟩

/-- 元の終点の同じ Yoneda 恒等点から、同じ pointed 終点への実際の辺。 -/
def twistedArrowPointedTargetEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).val
      (twistedArrowPointedEdgeVertex f) := by
  let e : SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C))
      (ULift.up (SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowEdgeVertex f)) :=
    ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f),
      congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex_src f),
      congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex_tgt f)⟩
  have h := e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C)
  exact ⟨h.edge, h.src_eq.trans (twistedArrowPointedDisplay_identity _), h.tgt_eq⟩

/-- 同じ pointed 辺の元の一単体は、元の Tw 辺の同じ全体の射による像。 -/
lemma twistedArrowPointedSourceEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (twistedArrowPointedSourceEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋1⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f)) := by
  unfold twistedArrowPointedSourceEdge
  rfl

/-- 同じ pointed 辺の元の一単体は、元の Tw 辺の同じ全体の射による像。 -/
lemma twistedArrowPointedTargetEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (twistedArrowPointedTargetEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay C).app (Opposite.op ⦋1⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f)) := by
  unfold twistedArrowPointedTargetEdge
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
