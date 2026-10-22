module

public import SerrePositivity.InfinityCategories.F2.VertexIsoEndpointTransport

/-!
概要：元の二つの指定頂点同型の合成を、明示した三頂点の等式で表示変更する。
方針：頂点等式の消去と、同じ型の指定同型の等式の消去を使う。
規約：指定値を選び直さない。使われ方：元の三辺の比較による三角形比較の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定した三頂点と二つの指定同型の表示変更は、合成の指定値も保持する。 -/
lemma vertexIso_trans_heq_of_heq {X : SSet.{u}} {a b c a' b' c' : X _⦋0⦌}
    (f : VertexIso a b) (g : VertexIso b c) (f' : VertexIso a' b') (g' : VertexIso b' c')
    (ha : a = a') (hb : b = b') (hc : c = c') (hf : HEq f f') (hg : HEq g g') :
    HEq (f ≪≫ g) (f' ≪≫ g') := by
  subst a' b' c'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- 同じ元の指定頂点同型の表示変更は、その逆の指定値も保持する。 -/
lemma vertexIso_symm_heq_of_heq {X : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (f : VertexIso a b) (f' : VertexIso a' b') (ha : a = a') (hb : b = b')
    (hf : HEq f f') : HEq f.symm f'.symm := by
  subst a' b'
  cases eq_of_heq hf
  rfl

end SerrePositivity.InfinityCategories.F2
