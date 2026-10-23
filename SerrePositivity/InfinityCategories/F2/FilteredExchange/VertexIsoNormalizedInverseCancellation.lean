module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：指定した同じ三同型の消去を、実二端点の明示的な表示変更後にも保持する。
方針：端点等式を消去し、元の合成式の逆を取る。
規約：指定同型を再選択しない。使われ方：下側輸送因子と定値三角形の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三同型の消去は、始点と最終点だけを同じ等式で揃えた後にも値まで成立する。 -/
lemma vertexIsoOfEq_inverse_cancel {X : SSet.{u}} {a b c a' c' : X _⦋0⦌}
    (t : VertexIso a b) (l : VertexIso a c) (r : VertexIso b c)
    (ha : a = a') (hc : c = c') (h : t.symm ≪≫ l = r) :
    (vertexIsoOfEq l ha hc).symm ≪≫ vertexIsoOfEq t ha rfl =
      vertexIsoOfEq r.symm hc rfl := by
  subst a' c'
  have hi := congrArg Iso.symm h
  simpa only [vertexIsoOfEq, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
    Iso.trans_symm, Iso.symm_symm_eq] using hi

end SerrePositivity.InfinityCategories.F2
