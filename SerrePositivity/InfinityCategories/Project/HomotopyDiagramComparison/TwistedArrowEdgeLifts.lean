module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TwistedArrowEdgeProjections
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Source
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaTargetBaseChange

/-!
概要：元の二つの Tw 辺を、始点固定と終点固定の実際の全空間へ持ち上げる。
方針：元の両射影の厳密な式を pullback の可換性として使う。
規約：辺を選び直さず、元の同じ一単体と反転した底を保持する。
使われ方：同じ Tw 全体の復元射を経る二方向の恒等点輸送の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の辺の反転単体を、同じ標準区間を始域とする射で表示する。 -/
def twistedArrowOppositeEdge {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (Δ[1] : SSet.{u}) ⟶ C.op :=
  SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))

/-- 始点側 Tw 辺は、同じ元の辺と始点固定の包含を被覆する。 -/
lemma twistedArrowSourceEdge_projection {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C =
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (SSet.opObjEquiv.symm (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) 1,
      SSet.yonedaEquiv f)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex_right]

/-- 終点側 Tw 辺は、同じ元の反転辺と終点固定の包含を被覆する。 -/
lemma twistedArrowTargetEdge_projection {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C =
      twistedArrowOppositeEdge f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [twistedArrowOppositeEdge, Equiv.apply_symm_apply]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f)) =
    (SSet.opObjEquiv.symm (SSet.yonedaEquiv f),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) 1)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex_right]

/-- 同じ始点側の辺を元の始点固定 Tw 全空間へ持ち上げる。 -/
def twistedArrowSourceEdgeLift {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) :=
  pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f)) f
    (twistedArrowSourceEdge_projection f)

/-- 同じ終点側の辺を元の終点固定 Tw 全空間へ持ち上げる。 -/
def twistedArrowTargetEdgeLift {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTarget
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) :=
  pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f))
    (twistedArrowOppositeEdge f) (twistedArrowTargetEdge_projection f)

/-- 始点固定へ持ち上げた辺の全体への像は、元の同じ辺。 -/
lemma twistedArrowSourceEdgeLift_fst {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    twistedArrowSourceEdgeLift f ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f) := pullback.lift_fst _ _ _

/-- 終点固定へ持ち上げた辺の全体への像も、元の同じ辺。 -/
lemma twistedArrowTargetEdgeLift_fst {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    twistedArrowTargetEdgeLift f ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))) =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f) := pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
