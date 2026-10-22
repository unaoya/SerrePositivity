module

public import SerrePositivity.InfinityCategories.F2.VertexIsoEndpointTransport

/-!
概要：二辺の共通終点消去式から、実端点の表示を保持して二つの恒等因子を除く。
方針：実頂点の等式を消去して同じ型で元の恒等同型の値を代入する。
規約：端点等式と指定同型の恒等性を別々の明示データとして使う。
使われ方：左右精密化の比較を元の二つの path と元の端点成分へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ消去式の二恒等因子を除いても、元の両端成分は同じ表示変更だけを受ける。 -/
lemma vertexIso_span_remove_constant {Y : SSet.{u}} {a b p c d q : Y _⦋0⦌}
    (A : VertexIso a b) (B : VertexIso q d) (L : VertexIso p b) (R : VertexIso c d)
    (S₀ : VertexIso a c) (S₁ : VertexIso p q) (ha : a = b) (hb : q = d)
    (hA : HEq A (Iso.refl (SSet.HomotopyCategory.mk b)))
    (hB : HEq B (Iso.refl (SSet.HomotopyCategory.mk d)))
    (h : L ≪≫ A.symm ≪≫ S₀ ≪≫ R = S₁ ≪≫ B) :
    L ≪≫ vertexIsoOfEq S₀ ha rfl ≪≫ R = vertexIsoOfEq S₁ rfl hb := by
  subst a
  subst q
  have heA : A = Iso.refl _ := eq_of_heq hA
  have heB : B = Iso.refl _ := eq_of_heq hB
  subst A
  subst B
  simpa only [vertexIsoOfEq, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl] using h

end SerrePositivity.InfinityCategories.F2
