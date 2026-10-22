module

public import SerrePositivity.InfinityCategories.F2.VertexIsoCompositionTransport

/-!
概要：元の合成同型の実三頂点を、同じ三等式で別々に揃える。
方針：実頂点の等式だけを消去する。
規約：両指定値を保持。使われ方：五因子式の定値三角形と残りの二因子を分ける。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ三実頂点で合成を揃える操作は、二つの指定同型を別々に揃えた合成に等しい。 -/
lemma vertexIsoOfEq_trans {X : SSet.{u}} {a b c a' b' c' : X _⦋0⦌}
    (f : VertexIso a b) (g : VertexIso b c) (ha : a = a') (hb : b = b') (hc : c = c') :
    vertexIsoOfEq (f ≪≫ g) ha hc = vertexIsoOfEq f ha hb ≪≫ vertexIsoOfEq g hb hc := by
  subst a' b' c'
  simp only [vertexIsoOfEq, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2
