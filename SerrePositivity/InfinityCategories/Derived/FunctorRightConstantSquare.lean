module
public import SerrePositivity.InfinityCategories.F1B.FunctorHomSquare

/-!
概要：右辺が恒等の実関手正方形から三辺の合成関係を得る。
方針：実二三角形の合成関係を使う。規約：標的の充填性を仮定しない。
使われ方：slice prism の全パラメータ評価。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 右辺が恒等の実正方形は、左辺と上辺の合成を下辺に同定する。 -/
lemma functorHom_comp_eq_of_rightConstantSquare {A X : SSet.{u}} {U V W : A ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy U W) (t : SSet.Homotopy V W)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X)
    (hb : SSet.ι₀ ≫ Q = curry r.h)
    (ht : SSet.ι₁ ≫ Q = curry t.h)
    (hl : prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q = curry l.h)
    (hr : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (functorVertex W)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy t) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have h := homMk_comp_eq_of_square
    (functorEdgeOfSimplicialHomotopy r) (functorEdgeOfSimplicialHomotopy t)
    (functorEdgeOfSimplicialHomotopy l)
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (functorVertex W)) Q
    (by
      change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv hb)
    (by
      change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv ht)
    (by
      change Q.app (Opposite.op ⦋1⦌) (_, homotopyIntervalEdge.edge) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv hl)
    (by
      change Q.app (Opposite.op ⦋1⦌) (_, homotopyIntervalEdge.edge) = _
      rw [← hi]
      change SSet.yonedaEquiv (prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q) = _
      rw [hr]
      exact pinchedConstant_one (functorVertex W))
  simpa only [SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] using h.symm
end SerrePositivity.InfinityCategories
