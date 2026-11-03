module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：四因子の整合式の両外辺を、同じ値の指定同型へ表示変更する。
方針：元の頂点等式を消去し、同じ型の同型の等式へ戻す。
規約：中間の二比較の指定値を保持。使われ方：元の三角形の値の整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 両外辺を元の指定値へ戻しても同じ中間比較と四因子の整合式を保持する。 -/
lemma vertexIso_four_factor_replace_edges {X : SSet.{u}}
    {a b c d e a' b' d' e' : X _⦋0⦌}
    (A : VertexIso a b) (B : VertexIso b c) (S : VertexIso c d)
    (R : VertexIso d e) (T : VertexIso a e)
    (A' : VertexIso a' b') (R' : VertexIso d' e')
    (ha : a = a') (hb : b = b') (hd : d = d') (he : e = e')
    (hA : HEq A A') (hR : HEq R R') (h : A ≪≫ B ≪≫ S ≪≫ R = T) :
    A' ≪≫ vertexIsoOfEq (B ≪≫ S) hb hd ≪≫ R' = vertexIsoOfEq T ha he := by
  subst a' b' d' e'
  cases eq_of_heq hA
  cases eq_of_heq hR
  simpa only [vertexIsoOfEq, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
