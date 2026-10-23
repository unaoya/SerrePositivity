module

public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleTriangleCancellation

/-!
概要：同じ二単体の二つの短辺が可逆なら長辺も可逆。
方針：元の二単体の同じ合成関係をホモトピー圏へ写す。
規約：追加の充填性や辺の選び直しは不要。
使われ方：二回目の元の底変換比較と結合比較を可逆三角形にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の同じ三角形の二つの短辺が可逆なら、長辺も可逆。 -/
lemma isInvertibleEdge_triangle_long_of_first_second {X : SSet.{u}} (t : X _⦋2⦌)
    (hfirst : IsInvertibleEdge (edgeOfSimplex (X.δ (2 : Fin 3) t)))
    (hsecond : IsInvertibleEdge (edgeOfSimplex (X.δ (0 : Fin 3) t))) :
    IsInvertibleEdge (edgeOfSimplex (X.δ (1 : Fin 3) t)) := by
  obtain ⟨x, y, z, f, g, h, c, rfl⟩ := SSet.Edge.CompStruct.exists_of_simplex t
  have : IsInvertibleEdge f.toTruncated := (isInvertibleEdge_congr c.d₂).mp hfirst
  have : IsInvertibleEdge g.toTruncated := (isInvertibleEdge_congr c.d₀).mp hsecond
  have hh : IsInvertibleEdge h.toTruncated := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk h.toTruncated)
    rw [← SSet.Truncated.HomotopyCategory.homMk_comp_homMk c.toTruncated]
    infer_instance
  exact (isInvertibleEdge_congr c.d₁).mpr hh

end SerrePositivity.InfinityCategories
