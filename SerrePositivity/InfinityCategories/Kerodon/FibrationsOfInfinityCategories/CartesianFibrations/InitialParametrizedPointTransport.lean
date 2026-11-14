module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointHomIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ParametrizedFiberTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomActionComparison

/-!
概要：全空間の始対象を指定点として評価した、実際の全区間パラメーターの輸送は同値。
方針：元の全左 Hom の円柱による輸送と比較し、その区間比較の同値を消去する。
規約：元の parametrizedFiberTransport の射そのもの。任意の left fibration に適用する。
使われ方：始点固定の Tw の恒等点からの輸送を、Yoneda の実際の区間 Hom 作用で判定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 元の左 Hom 円柱による指定点の作用は、同じ区間比較後の普遍輸送の評価と関手同型。 -/
def pointHomTransportActionAt_parametrizedIso {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a b : B _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportActionAt p a b v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointHomIntervalComparison a b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) := by
  have h := ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomFiberTransport p a b).mapIso_parametrized p
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism a b) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism_zero a b)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism_one a b)).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
  have he : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomFiberTransport p a b).map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportActionAt p a b v := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily.map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
    rfl
  rw [he] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointHomIntervalComparison, Category.assoc] using h

/-- 全空間の始対象を指定点とする、同じ全区間パラメーターの普遍輸送の評価は同値。 -/
lemma parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (d : E _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p (p.app (Opposite.op ⦋0⦌) d) b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomSourceVertex p d)) := by
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily_homotopyEquivalence p d b hd
  have h := h₀.isQCatEquivalence
  have hA := h.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomActionComparisonHomotopy p d b))
  have hP := hA.ofFunctorIso (pointHomTransportActionAt_parametrizedIso p
    (p.app (Opposite.op ⦋0⦌) d) b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomSourceVertex p d))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointHomIntervalComparison_isQCatEquivalence _ _).cancel_left hP

/-- 同じ指定 fiber の点が全空間の始対象なら、その点での普遍輸送の評価は同値。 -/
lemma parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialFiberPoint
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a b : B _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) := by
  rcases v with ⟨d, hd⟩
  have ha : p.app (Opposite.op ⦋0⦌) d = a := hd.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  subst a
  exact parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex p d hv b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
