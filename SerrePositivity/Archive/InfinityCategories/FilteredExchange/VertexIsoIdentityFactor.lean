module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の指定頂点同型の恒等因子を、元の頂点等式を保って像と合成から除く。
方針：明示した頂点等式を消去し、恒等同型の関手性と合成則を使う。
規約：指定値を保持。使われ方：固定 Kan 射の二側比較の恒等因子の除去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定同型が実終点の恒等の値なら、その像も実終点像の恒等の値。 -/
lemma vertexIso_map_heq_refl_of_heq {X Y : SSet.{u}} {a b : X _⦋0⦌}
    (c : VertexIso a b) (hab : a = b)
    (hc : HEq c (Iso.refl (SSet.HomotopyCategory.mk b))) (m : X ⟶ Y) :
    HEq (VertexIso.map c m)
      (Iso.refl (SSet.HomotopyCategory.mk (m.app (Opposite.op ⦋0⦌) b))) := by
  have h := vertexIso_map_heq_of_heq c (Iso.refl (SSet.HomotopyCategory.mk b)) hab rfl hc m
  simpa only [VertexIso.map, CategoryTheory.Functor.mapIso_refl, hoFunctor_map,
    Functor.toCatHom_toFunctor, mapHomotopyCategory_obj_mk] using h

/-- 右因子が同じ実終点の恒等の値なら、元の左因子の値だけが残る。 -/
lemma vertexIso_trans_heq_of_right_refl {X : SSet.{u}} {a b c : X _⦋0⦌}
    (A : VertexIso a b) (B : VertexIso b c) (hbc : b = c)
    (hB : HEq B (Iso.refl (SSet.HomotopyCategory.mk c))) : HEq (A ≪≫ B) A := by
  subst c
  cases eq_of_heq hB
  simp only [Iso.trans_refl]
  rfl

end SerrePositivity.InfinityCategories.F2
