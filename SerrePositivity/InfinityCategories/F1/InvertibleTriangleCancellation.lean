module

public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：同じ二単体の最初の辺と長辺が可逆なら、次の辺も可逆。
方針：元の二単体の合成関係をホモトピー圏へ写し、同じ可逆射を打ち消す。
規約：単体集合の追加の充填性は要求しない。
使われ方：元の底変換比較三角形の全ての辺の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ一単体を表す元の辺から、その標準端点表示へ可逆性を移す。 -/
lemma isInvertibleEdge_edgeOfSimplex_of_eq {X : SSet.{u}} (s : X _⦋1⦌)
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : s = e.edge) (he : IsInvertibleEdge e) : IsInvertibleEdge (edgeOfSimplex s) :=
  (isInvertibleEdge_congr h).mpr he

/-- 元の辺の可逆性を、同じ一単体の標準端点表示へ移す。 -/
lemma isInvertibleEdge_edgeOfSimplex {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Edge x y) (he : IsInvertibleEdge e.toTruncated) :
    IsInvertibleEdge (edgeOfSimplex e.edge) :=
  isInvertibleEdge_edgeOfSimplex_of_eq e.edge e.toTruncated rfl he

/-- 元の同じ三角形の最初の辺と長辺の可逆性は、次の辺の可逆性を与える。 -/
lemma isInvertibleEdge_triangle_second_of_first_long {X : SSet.{u}} (t : X _⦋2⦌)
    (hfirst : IsInvertibleEdge (edgeOfSimplex (X.δ (2 : Fin 3) t)))
    (hlong : IsInvertibleEdge (edgeOfSimplex (X.δ (1 : Fin 3) t))) :
    IsInvertibleEdge (edgeOfSimplex (X.δ (0 : Fin 3) t)) := by
  obtain ⟨x, y, z, f, g, h, c, rfl⟩ := SSet.Edge.CompStruct.exists_of_simplex t
  haveI : IsInvertibleEdge f.toTruncated :=
    (isInvertibleEdge_congr c.d₂).mp hfirst
  haveI : IsInvertibleEdge h.toTruncated :=
    (isInvertibleEdge_congr c.d₁).mp hlong
  have hc := SSet.Truncated.HomotopyCategory.homMk_comp_homMk c.toTruncated
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk f.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk g.toTruncated) := by
    rw [hc]
    infer_instance
  have hg : IsInvertibleEdge g.toTruncated := IsIso.of_isIso_comp_left
    (SSet.Truncated.HomotopyCategory.homMk f.toTruncated)
    (SSet.Truncated.HomotopyCategory.homMk g.toTruncated)
  exact (isInvertibleEdge_congr c.d₀).mpr hg

end SerrePositivity.InfinityCategories
