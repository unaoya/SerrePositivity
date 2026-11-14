module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomotopyEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyPathReplacement

/-!
概要：一点からの同じ可逆 path を元のホモトピーの点評価の一単体へ戻す。
方針：curry と因子交換を展開し、同じ代表辺を回収する。
規約：可逆 path の辺の類を選び直さない。使われ方：指定境界経路の修正辺の類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 一点での可逆 path の辺は、同じ元の円柱の点評価そのもの。 -/
lemma homotopyEquivalencePath_point_diagram {X : SSet.{u}} [KanComplex X]
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g) :
    SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath H)).val) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
    ((curry ((β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫ H.h)).app _
      (stdSimplex.obj₀Equiv.symm 0)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
  rfl

/-- 同じ path の一単体を持つ辺の類は、元の関手同型の一点評価である。 -/
lemma homotopyEquivalencePath_point_hom_arrow {X : SSet.{u}} [KanComplex X]
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g) (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (hI : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = I.hom)
    {a b : X _⦋0⦌} (s : X.Edge a b)
    (hs : s.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath H)).val) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk s.toTruncated) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomotopy_evaluation_hom_arrow H I hI s
    ((congrArg SSet.yonedaEquiv.symm hs).trans (homotopyEquivalencePath_point_diagram H))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
