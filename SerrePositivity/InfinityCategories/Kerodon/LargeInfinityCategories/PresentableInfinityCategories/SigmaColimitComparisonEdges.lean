module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafApexRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafColimitLegClasses

/-!
概要：実際の有限錐像と標準有限積全錐の間で、同じ coslice 代表の頂点辺を保持する。
方針：実際の評価頂点・標準余極限頂点の等式だけで両端を揃える。
規約：全脚で同じ頂点代表を共有し、元の可逆辺の全一単体を変更しない。
使われ方：完成済み全脚正方形の全錐移送判定への入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
local notation "x₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r x₀
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteEvaluationFamily r (p := p)

/-- 同じ元の頂点比較辺を、実際の全錐像と標準全錐の同じ頂点間で保持する。 -/
def sigmaColimitApexComparisonEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c)).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafColimitFiniteCone r c).vertex :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge
    (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) q hq x₀)).ofEq
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeEvaluation_vertex q x₀).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c)).symm)
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex A).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject A)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafColimitFiniteCone_vertex r c).symm))

/-- 同じ元の各点比較辺を、実際の図式と標準全錐の図式の同じ成分間で保持する。 -/
def sigmaColimitComponentComparisonEdge (j : J) :
    SSet.Edge
      (((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (Discrete.functor
        (fun j => _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (G j)))).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge
    (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) q hq
    (ULift.up (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))))).ofEq
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeEvaluation_vertex q _)
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex (G j)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex (Discrete.functor
          (fun j => _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (G j))) (Discrete.mk j)).symm)

/-- 元の全錐頂点間へ正規化しても、同じ元の頂点比較辺は可逆。 -/
lemma sigmaColimitApexComparisonEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (sigmaColimitApexComparisonEdge r q hq c).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (sigmaColimitApexComparisonEdge r q hq c).toTruncated)
    (f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge
      (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) q hq x₀) rfl).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge_isInvertible _ _ _ _

omit [Finite J] [Nonempty J] in
/-- 元の図式成分間へ正規化しても、同じ元の各点比較辺は可逆。 -/
lemma sigmaColimitComponentComparisonEdge_isInvertible (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated)
    (f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) q hq
      (ULift.up (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))) rfl).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge_isInvertible _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
