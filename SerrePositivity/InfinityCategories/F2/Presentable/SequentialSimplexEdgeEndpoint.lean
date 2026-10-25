module

public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialSimplexEdgeExtension
public import SerrePositivity.InfinityCategories.Core.OuterHornJoin

/-!
概要：指定辺で延長した全単体の最終頂点を回収する。
方針：余錐の頂点と最後の辺の終点を、同じ標準単体の零次の制限で比較する。
規約：頂点の等式は全単体延長の制限から導く。
使われ方：指定された可算辺列の次の延長を同じ終点で開始する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：標準単体を余錐として読んだ頂点は元の最終頂点。
方針：右因子への制限を最終頂点の写像に直す。
規約：元の頂点の厳密な等式。
使われ方：指定辺の始点条件を正規化する。 -/
lemma simplexTerminalCocone_vertex {X : SSet.{u}} (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    (simplexTerminalCocone n f).vertex =
      SSet.yonedaEquiv (SSet.stdSimplex.map (PinchedHom.lastVertex n) ≫ f) := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv
    (joinInr Δ[n] Δ[0] ≫ ((joinStdSimplexIso n 0).hom ≫ f)) = _
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr]

/-- 概要：最後の辺の終点は結合した標準単体の最終頂点。
方針：右辺の標準単体表示の終点を計算する。
規約：標準零単体からの全射の等式。
使われ方：指定辺延長の終点の回収。 -/
lemma joinStdSimplexIso_rightEdge_lastVertex (n : ℕ) :
    SSet.stdSimplex.map (PinchedHom.lastVertex (n + 1)) =
      SSet.stdSimplex.δ (0 : Fin 2) ≫
        (joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso n 1).hom) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, joinStdSimplexIso_inr_edge]
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 概要：指定辺で延長した単体の最終頂点は指定辺の終点そのもの。
方針：最後の辺への制限とその時刻一への制限を合成する。
規約：元の指定辺の終点を厳密に保持する。
使われ方：可算辺列の延長を再帰的に反復する。 -/
lemma simplexSpecifiedEdgeExtension_vertex {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) {y : X _⦋0⦌}
    (e : X.Edge (simplexTerminalCocone n f).vertex y) :
    (simplexTerminalCocone (n + 1) (simplexSpecifiedEdgeExtension n f e)).vertex = y := by
  rw [simplexTerminalCocone_vertex, joinStdSimplexIso_rightEdge_lastVertex,
    Category.assoc, simplexSpecifiedEdgeExtension_lastEdge,
    e.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2.Presentable
