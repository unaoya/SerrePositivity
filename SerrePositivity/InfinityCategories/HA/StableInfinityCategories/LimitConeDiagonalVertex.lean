module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareDiagonalEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeSquareReadback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LimitConeVertexTransport

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma exists_limitCone_vertex_diagonal {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    {a : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      a c.vertex)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧ d.vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge) := by
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (uncurry (SSet.yonedaEquiv.symm e.edge))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_functorEdge_edge e)).2 he
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_squareDiagonalArrow_equivalence
    (uncurry (SSet.yonedaEquiv.symm e.edge)) hl
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_functorEdge_vertex e
  let g : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge)) c.vertex :=
    ⟨f.edge, f.src_eq, f.tgt_eq.trans ht⟩
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Edge.ofTruncated g) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show (SSet.Edge.ofTruncated g).edge = f.edge from rfl)).2 hf
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_limitCone_vertex_of_invertible c hc (SSet.Edge.ofTruncated g) hg

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
