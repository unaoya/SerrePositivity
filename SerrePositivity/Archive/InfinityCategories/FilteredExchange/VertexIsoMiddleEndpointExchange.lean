module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointComposition

/-!
概要：同じ指定後続同型の二つの実始点表示を、元の前置比較の終点表示へ移す。
方針：元の三頂点等式だけを消去する。
規約：指定二因子を保持。使われ方：模型五因子式の中間頂点の厳密な変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 後続同型の始点表示の変更は、同じ前置比較の終点だけへ厳密に移せる。 -/
lemma vertexIsoOfEq_change_middle {X : SSet.{u}} {a b b' c x y : X _⦋0⦌}
    (r : VertexIso a b) (g : VertexIso x y) (hx : x = b) (hx' : x = b') (hy : y = c) :
    r ≪≫ vertexIsoOfEq g hx hy =
      vertexIsoOfEq r rfl (hx.symm.trans hx') ≪≫ vertexIsoOfEq g hx' hy := by
  cases hx
  cases hx'
  cases hy
  simp only [vertexIsoOfEq, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2
