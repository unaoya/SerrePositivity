module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges

/-! # 元の実閉辺の厳密等式と閉合成の厳密等式

概要：型付き閉射は実一次単体で判定でき、端点族が違っても同じ実辺の合成を比較できる。
方針：一次単体の対象を評価して端点等式を消去し、閉射の回収の両逆性を使う。
規約：辺全体の厳密等式。使われ方：有限同時細分の全新始頂点を共通化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 同じ元の端点を持つ閉射は、その実一次単体の厳密等式で判定できる。 -/
lemma dgClosedEdge_raw_injective {x y : D}
    (r s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (h : (dgClosedEdge A D r).edge = (dgClosedEdge A D s).edge) : r = s := by
  have he := Truncated.Edge.ext h
  have hc := congrArg (fun e : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
    (Simplex.vertex x) (Simplex.vertex y) => edgeClosed e) he
  simpa only [dgClosedEdge_closed] using hc

/-- 新旧の型付き端点族が違っても、同じ二実閉辺の合成の実辺は厳密に同じ。 -/
lemma dgClosedEdge_comp_of_edge_eq {p x y p' x' y' : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) x)
    (r' : ForgetEnrichment.of (Complex A) p' ⟶ ForgetEnrichment.of (Complex A) x')
    (g : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (g' : ForgetEnrichment.of (Complex A) x' ⟶ ForgetEnrichment.of (Complex A) y')
    (hR : (dgClosedEdge A D r).edge = (dgClosedEdge A D r').edge)
    (hG : (dgClosedEdge A D g).edge = (dgClosedEdge A D g').edge) :
    (dgClosedEdge A D (r ≫ g)).edge = (dgClosedEdge A D (r' ≫ g')).edge := by
  have hp : p = p' := congrArg (fun t : Simplex A D 1 => t.obj 0) hR
  have hx : x = x' := congrArg (fun t : Simplex A D 1 => t.obj 1) hR
  have hy : y = y' := congrArg (fun t : Simplex A D 1 => t.obj 1) hG
  cases hp
  cases hx
  cases hy
  cases dgClosedEdge_raw_injective A D r r' hR
  cases dgClosedEdge_raw_injective A D g g' hG
  rfl

end SerrePositivity.InfinityCategories
