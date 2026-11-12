module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 同じ元の端点を持つ閉射は、その実一次単体の厳密等式で判定できる。 -/
lemma dgClosedEdge_raw_injective {x y : D}
    (r s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge) : r = s := by
  have he := Truncated.Edge.ext h
  have hc := congrArg (fun e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) he
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] using hc

/-- 新旧の型付き端点族が違っても、同じ二実閉辺の合成の実辺は厳密に同じ。 -/
lemma dgClosedEdge_comp_of_edge_eq {p x y p' x' y' : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (r' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x')
    (g : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (g' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y')
    (hR : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r').edge)
    (hG : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g').edge) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (r ≫ g)).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (r' ≫ g')).edge := by
  have hp : p = p' := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 0) hR
  have hx : x = x' := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 1) hR
  have hy : y = y' := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 1) hG
  cases hp
  cases hx
  cases hy
  cases dgClosedEdge_raw_injective A D r r' hR
  cases dgClosedEdge_raw_injective A D g g' hG
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
