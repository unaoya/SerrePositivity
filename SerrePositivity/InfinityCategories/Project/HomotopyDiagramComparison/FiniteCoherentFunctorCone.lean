module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteConeFromEdges
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteCoherentProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence

/-!
概要：元の反復 coherent 積と元の全射影を、関手圏内の一つの native 全錐にまとめる。
方針：各射影変換の同じ辺を使って離散図式の全錐を構成し、全評価を厳密に照合する。
規約：元の積関手・全射影辺を保持。極限性は別途証明する。
使われ方：元の評価極限錐の族との比較、P_Σ の sifted 閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))

/-- 元の有限族を、元の関手 ∞ 圏の離散図式として表示する。 -/
def finiteCoherentFunctorDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete (ULift.{u} (Fin (n + 1))))) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F i.down))

/-- 元の離散関手図式の各頂点は、元の指定された関手そのもの。 -/
lemma finiteCoherentFunctorDiagram_vertex (i : ULift.{u} (Fin (n + 1))) :
    (finiteCoherentFunctorDiagram n F).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i))) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F i.down) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap_vertex _ _

/-- 元の射影変換を、元の関手図式の指定頂点に向かう同じ辺として表示する。 -/
def finiteCoherentFunctorProjection (i : ULift.{u} (Fin (n + 1))) :
    SSet.Truncated.Edge (X := (truncation 2).obj
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F))
      ((finiteCoherentFunctorDiagram n F).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))) :=
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.down)
  ⟨q.edge, q.src_eq, q.tgt_eq.trans (finiteCoherentFunctorDiagram_vertex n F i).symm⟩

/-- 元の反復積関手と全射影変換からなる、関手 ∞ 圏内の native 全錐。 -/
def finiteCoherentFunctorCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (finiteCoherentFunctorDiagram n F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeFromEdges _ (finiteCoherentFunctorProjection n F)

/-- 元の全錐の頂点は、元の反復積関手そのもの。 -/
lemma finiteCoherentFunctorCone_vertex :
    (finiteCoherentFunctorCone n F).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeFromEdges_vertex _ _

/-- 元の全錐の各脚は、元の反復射影変換の同じ全一単体。 -/
lemma finiteCoherentFunctorCone_leg_edge (i : ULift.{u} (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (finiteCoherentFunctorCone n F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.down)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeFromEdges_leg_edge _ _ _

/-- 元の関手図式の評価は、元の各関手の評価値を持つ同じ離散図式。 -/
lemma finiteCoherentFunctorDiagram_evaluation
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram (finiteCoherentFunctorDiagram n F) b =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap (fun i : ULift.{u} (Fin (n + 1)) ↦
        (F i.down).app (Opposite.op ⦋0⦌) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram, finiteCoherentFunctorDiagram, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap_postcomp]
  congr 1
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b (F i.down)

/-- 元の全錐を評価した頂点は、元の反復積関手の評価値。 -/
lemma finiteCoherentFunctorCone_evaluation_vertex
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (finiteCoherentFunctorCone n F) b).vertex =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F).app (Opposite.op ⦋0⦌) b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone_vertex, finiteCoherentFunctorCone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]

/-- 元の全錐の評価した各脚は、元の反復射影辺の評価そのもの。 -/
lemma finiteCoherentFunctorCone_evaluation_leg
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)
    (i : ULift.{u} (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (finiteCoherentFunctorCone n F) b)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.down)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (finiteCoherentFunctorCone n F) _).edge = _
  rw [finiteCoherentFunctorCone_leg_edge]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
