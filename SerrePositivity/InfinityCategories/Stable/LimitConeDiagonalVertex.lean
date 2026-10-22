module
public import SerrePositivity.InfinityCategories.Stable.SquareDiagonalEquivalence
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeSquareReadback
public import SerrePositivity.InfinityCategories.Stable.LimitConeVertexTransport

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
namespace SerrePositivity.InfinityCategories

lemma exists_limitCone_vertex_diagonal {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X}
    (c : JoinCone p) (hc : IsLimitCone c)
    {a : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      a c.vertex)
    (he : IsInvertibleEdge (e.map ((truncation 2).map
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))) :
    ∃ d : JoinCone p, IsLimitCone d ∧ d.vertex =
      functorVertex (SSet.yonedaEquiv.symm
        (squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge) := by
  have hl : IsInvertibleEdge
      (squareLeftArrow (uncurry (SSet.yonedaEquiv.symm e.edge))) :=
    (isInvertibleEdge_congr (squareLeftArrow_functorEdge_edge e)).2 he
  obtain ⟨f, hf⟩ := exists_squareDiagonalArrow_equivalence
    (uncurry (SSet.yonedaEquiv.symm e.edge)) hl
  have ht := squareTopArrow_functorEdge_vertex e
  let g : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (functorVertex (SSet.yonedaEquiv.symm
        (squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge)) c.vertex :=
    ⟨f.edge, f.src_eq, f.tgt_eq.trans ht⟩
  have hg : IsInvertibleEdge (SSet.Edge.ofTruncated g) :=
    (isInvertibleEdge_congr (show (SSet.Edge.ofTruncated g).edge = f.edge from rfl)).2 hf
  exact exists_limitCone_vertex_of_invertible c hc (SSet.Edge.ofTruncated g) hg

end SerrePositivity.InfinityCategories
