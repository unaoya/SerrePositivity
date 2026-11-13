module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitHomotopyPointwise
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalFamilyHomotopy

/-!
概要：同値矢印の coherent 図式の元の点ごとの余極限頂点も同値矢印。
方針：矢印の全余錐を円柱に読み替え、両端の普遍余錐の比較へ可逆性を反映する。
規約：元の余錐と完成後の矢印を保持。使われ方：単体形状の有限極限交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 両端が余極限で各値が同値矢印なら、元の完成後の矢印も可逆。 -/
lemma isEquivalencePathVertex_colimitVertex {J X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hp : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (p.app (Opposite.op ⦋0⦌) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex c.vertex := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.arrowFamilyHomotopy c.val
  have hj : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)).toTruncated := by
    intro j
    have he := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.arrowFamilyHomotopy_vertex_edge c.val
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)
    have hv : c.val.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j) = p.app (Opposite.op ⦋0⦌) j :=
      ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) j
    rw [hv] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hp j)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitHomotopy_vertex_isInvertible
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h0 h1 H hj
  have he := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.arrowFamilyHomotopy_vertex_edge c.val
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr J Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have hv : c.val.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr J Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))) = c.vertex := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, SSet.yonedaEquiv_comp]
    rfl
  rw [hv] at he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp h

/-- 元の点ごとの余極限余錐には、同値矢印の条件も保存される。 -/
lemma isEquivalencePathVertex_of_pointwiseColimit {J X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c)
    (hp : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (p.app (Opposite.op ⦋0⦌) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex c.vertex :=
  isEquivalencePathVertex_colimitVertex c (hc _) (hc _) hp

end SerrePositivity.InfinityCategories.Project.FilteredExchange
