module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.FiniteCoherentFunctorCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative

/-!
概要：元の反復積関手の評価錐を、元の Kan 値族と反復 Kan 積の同じ頂点で表示する。
方針：元の各図式の値を Kan 対象へ戻し、図式は全頂点、頂点は二項積の値で照合する。
規約：元の全評価錐の射を保持。極限性と射影のホモトピーは別途証明する。
使われ方：元の評価脚から native 有限積の極限判定への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)

/-- 元の各関手を同じ点で評価した Kan 対象の有限族。 -/
def finiteFunctorKanValues (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((F i).app (Opposite.op ⦋0⦌) b)

/-- 元の反復積関手の値は、元の各 Kan 値の同じ反復積の標準頂点。 -/
lemma finiteCoherentSpaceProduct_vertex :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F).app (Opposite.op ⦋0⦌) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (finiteFunctorKanValues n F b)) := by
  induction n with
  | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm
  | succ n ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct_vertex, ih]
    rfl

/-- 元の評価図式は、元の各 Kan 値の図式の coherent 表示そのもの。 -/
lemma finiteCoherentFunctorEvaluationDiagram_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentFunctorDiagram n F) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (finiteFunctorKanValues n F b)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentFunctorDiagram_evaluation]
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm

/-- 元の評価全錐を、元の Kan 値族の厳密に同じ図式上に表示する。 -/
def finiteFunctorEvaluationCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (finiteFunctorKanValues n F b))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentFunctorCone n F) b).cast
    (finiteCoherentFunctorEvaluationDiagram_eq n F b)

/-- 元の評価全錐の頂点は、元の Kan 値族の同じ反復積。 -/
lemma finiteFunctorEvaluationCone_vertex :
    (finiteFunctorEvaluationCone n F b).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (finiteFunctorKanValues n F b)) := by
  rw [finiteFunctorEvaluationCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentFunctorCone_evaluation_vertex, finiteCoherentSpaceProduct_vertex]

/-- 元の評価全錐の各脚を、同じ反復 Kan 積からの元の射へ読み戻す。 -/
def finiteFunctorEvaluationKanLeg (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (finiteFunctorKanValues n F b) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (finiteFunctorKanValues n F b)).obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (finiteFunctorEvaluationCone n F b) _
    (finiteFunctorEvaluationCone_vertex n F b) i

/-- 読み戻した元の各 Kan 脚の辺は、元の反復射影変換の評価と同じ全一単体。 -/
lemma finiteFunctorEvaluationKanLeg_edge (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (finiteFunctorEvaluationKanLeg n F b i)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge (finiteFunctorEvaluationCone n F b) _
    (finiteFunctorEvaluationCone_vertex n F b) i).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentFunctorCone_evaluation_leg n F b i.as)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
