module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomotopyEvaluation

/-!
概要：関手の実際の円柱の点評価を、その円柱から作った関手同型の同じ成分へ接続する。
方針：評価した raw な一単体を照合し、既存の成分評価の等式を使う。
規約：標的の辺の一意性は使わない。使われ方：native な合成比較円柱の終点の類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ raw な点評価辺の類は、指定した関手同型の同じ頂点での成分である。 -/
lemma functorHomotopy_component_hom_arrow {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (hI : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = I.hom)
    (x : A _⦋0⦌) {a b : X _⦋0⦌} (t : X.Edge a b)
    (ht : SSet.yonedaEquiv.symm t.edge =
      lift (SSet.const x) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk t.toTruncated) =
      Arrow.mk (I.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) := by
  have he : t.edge = ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x))).edge := by
    apply SSet.yonedaEquiv.symm.injective
    exact ht.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomotopy_evaluation_diagram H x).symm
  refine (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk t.toTruncated
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x))) he).trans ?_
  exact (congrArg
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.mapArrow.obj
    (congrArg Arrow.mk hI)).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoComponent_hom_arrow I x).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
