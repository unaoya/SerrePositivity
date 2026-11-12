module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：指定頂点同型と可換正方形を、明示した元の頂点の等式に沿って表示変更する。
方針：端点の等号同型を合成し、正方形の移送は同じ等式の消去へ戻す。
規約：HEq から端点等式を取り出さない。使われ方：指定 prism 比較の自然性の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ指定頂点同型の両端の表示だけを、明示した頂点等式で揃える。 -/
def vertexIsoOfEq {X : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') : VertexIso a' b' :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk ha)).symm ≪≫ e ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hb)

/-- 両端の表示だけを変えても、元の指定同型の値を保持する。 -/
lemma vertexIsoOfEq_heq {X : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') : HEq (vertexIsoOfEq e ha hb) e :=
  iso_endpoints_heq e (congrArg SSet.HomotopyCategory.mk ha)
    (congrArg SSet.HomotopyCategory.mk hb)

/-- 元の四頂点と四つの指定値を保つ表示変更は、元の同じ可換正方形を保持する。 -/
lemma vertexIso_square_of_heq {X : SSet.{u}} {a b c d a' b' c' d' : X _⦋0⦌}
    (f : VertexIso a b) (g : VertexIso b d) (h : VertexIso a c) (i : VertexIso c d)
    (f' : VertexIso a' b') (g' : VertexIso b' d') (h' : VertexIso a' c') (i' : VertexIso c' d')
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (hf : HEq f f') (hg : HEq g g') (hh : HEq h h') (hi : HEq i i')
    (hs : f ≪≫ g = h ≪≫ i) : f' ≪≫ g' = h' ≪≫ i' := by
  subst a' b' c' d'
  cases eq_of_heq hf
  cases eq_of_heq hg
  cases eq_of_heq hh
  cases eq_of_heq hi
  exact hs

end SerrePositivity.InfinityCategories.F2
