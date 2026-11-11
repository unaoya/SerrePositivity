module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の四つの指定関手同型の正方形を、同じ四実射の等式で輸送する。
方針：四つの実射の等式と、元の指定同型の型付き一致を消去する。
規約：指定された四因子を保持。使われ方：単位因子の交換式の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 実射の四端点の表示を変えても、同じ四つの指定値の正方形は保持される。 -/
lemma functorIso_square_of_heq {X Y : SSet.{u}} {a b c d a' b' c' d' : X ⟶ Y}
    (f : FunctorIso a b) (g : FunctorIso b d) (h : FunctorIso a c) (i : FunctorIso c d)
    (f' : FunctorIso a' b') (g' : FunctorIso b' d')
    (h' : FunctorIso a' c') (i' : FunctorIso c' d')
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (hf : HEq f' f) (hg : HEq g' g) (hh : HEq h' h) (hi : HEq i' i)
    (hs : f ≪≫ g = h ≪≫ i) : f' ≪≫ g' = h' ≪≫ i' := by
  subst a' b' c' d'
  cases eq_of_heq hf
  cases eq_of_heq hg
  cases eq_of_heq hh
  cases eq_of_heq hi
  exact hs

end SerrePositivity.InfinityCategories.F2
