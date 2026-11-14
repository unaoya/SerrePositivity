module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.DiagonalEvaluationTransport

/-!
概要：元の全変換の点評価は、元の底辺による両図式の標準輸送と両立する。
方針：四辺を保持した元の正方形の全輸送比較を、同じ元の評価作用へ移す。
規約：全変換空間を一つのパラメータとして扱い、点ごとの自然性を仮定しない。
使われ方：Yoneda 評価の第一変数自然性の、反変輸送側との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の変換族と底辺から、元の四辺を保持した輸送正方形を構成する。 -/
def unstraighteningTransportSquare {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportIntervalSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
      (F.app _ a) (F.app _ b) (G.app _ a) (G.app _ b) where
  bottom := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (e.map F))
  top := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (e.map G))
  left := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningEvaluationInterval F G a
  right := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningEvaluationInterval F G b
  square := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningBaseSquare F G e
  zero := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningBaseSquare_zero F G e
  one := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningBaseSquare_one F G e
  inner_zero := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningBaseSquare_inner_zero F G e
  inner_one := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningBaseSquare_inner_one F G e

/-- 元の全 fiber Hom の評価は、同じ元の底辺に沿う両端の標準輸送と関手同型まで可換。 -/
def unstraighteningFiberEvaluation_baseTransportIso {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) a)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (e.map F)).app (Opposite.op ⦋0⦌) v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (e.map G)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  let s := unstraighteningTransportSquare F G e
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport p (SSet.const v) s.bottom)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.map F)).app (Opposite.op ⦋0⦌) v)) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagonalFiberTransport_edgeIso p (e.map F)
      (SSet.const (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) v)
    simp only [SSet.const_comp] at h
    exact h
  have ha := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningFiberEvaluation_diagonalIso F G a v
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningFiberEvaluation_diagonalIso F G b
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.map F)).app (Opposite.op ⦋0⦌) v)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport_sourceIso p hb s.right
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagonalFiberTransport_edgeIso p (e.map G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport p (SSet.const v) s.left)
  have h₄ := ha.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.map G))
  have h := hc ≪≫ h₂.symm ≪≫ s.transportIso p (SSet.const v) ≪≫ h₃ ≪≫ h₄.symm
  simp only [Category.assoc] at h
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
