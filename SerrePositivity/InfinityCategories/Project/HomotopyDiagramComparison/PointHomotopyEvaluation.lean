module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：一点からの関手の実際の円柱を評価し、同じ辺の類を回収する。
方針：curry と頂点評価を計算し、指定した代表辺の raw な図式と比較する。
規約：代表を選び直さない。使われ方：付加辺輸送の円柱と中間評価の辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 実際の関手ホモトピーの辺を頂点で評価すると、同じ raw な円柱の制限になる。 -/
lemma functorHomotopy_evaluation_diagram {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge) =
      lift (SSet.const x) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  rw [← SSet.yonedaEquiv_symm_comp]
  change curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex H.h x

/-- 同じ一点円柱を表す実際の辺の類は、指定済みの関手同型の点評価の射。 -/
lemma pointHomotopy_evaluation_hom_arrow {X : SSet.{u}}
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g) (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (hI : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = I.hom)
    {a b : X _⦋0⦌} (t : X.Edge a b)
    (ht : SSet.yonedaEquiv.symm t.edge =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk t.toTruncated) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).hom := by
  have he : t.edge = ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom)).edge := by
    apply SSet.yonedaEquiv.symm.injective
    exact ht.trans (functorHomotopy_evaluation_diagram H (stdSimplex.obj₀Equiv.symm 0)).symm
  refine (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk t.toTruncated
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom)) he).trans ?_
  exact congrArg
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).toFunctor.mapArrow.obj
    (congrArg Arrow.mk hI)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
