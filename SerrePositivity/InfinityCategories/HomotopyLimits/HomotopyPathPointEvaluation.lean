module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomotopyEvaluation
public import SerrePositivity.InfinityCategories.F1B.HomotopyPathReplacement

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 一点での可逆 path の辺は、同じ元の円柱の点評価そのもの。 -/
lemma homotopyEquivalencePath_point_diagram {X : SSet.{u}} [KanComplex X]
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g) :
    SSet.yonedaEquiv.symm
        (intervalFunctorVertexEdge (SSet.yonedaEquiv (homotopyEquivalencePath H)).val) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change intervalFunctorVertexEdge
    ((curry ((β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫ H.h)).app _
      (stdSimplex.obj₀Equiv.symm 0)) = _
  rw [intervalFunctorVertexEdge_curry]
  rfl

/-- 同じ path の一単体を持つ辺の類は、元の関手同型の一点評価である。 -/
lemma homotopyEquivalencePath_point_hom_arrow {X : SSet.{u}} [KanComplex X]
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g) (I : FunctorIso f g)
    (hI : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) = I.hom)
    {a b : X _⦋0⦌} (s : X.Edge a b)
    (hs : s.edge = intervalFunctorVertexEdge
      (SSet.yonedaEquiv (homotopyEquivalencePath H)).val) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk s.toTruncated) =
      Arrow.mk (VertexIso.map I (pointFunctorEvaluationIso X).hom).hom :=
  pointHomotopy_evaluation_hom_arrow H I hI s
    ((congrArg SSet.yonedaEquiv.symm hs).trans (homotopyEquivalencePath_point_diagram H))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
