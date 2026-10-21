module

public import Mathlib.CategoryTheory.Iso

/-!
概要：四頂点と指定同型の値の一致を保ち、同型の正方形を別の端点表示へ移す。
方針：明示した四つの対象の等式と同型の型付き一致だけを消去する。
規約：HEq から対象の等式を取り出さない。使われ方：native 可換式の宇宙下降。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 明示した四頂点の等式の下で、同じ指定四同型の正方形は可換性を保持する。 -/
lemma iso_square_transport {D : Type u} [Category.{v} D] {a b c d a' b' c' d' : D}
    (l : a ≅ b) (m : b ≅ d) (r : a ≅ c) (s : c ≅ d)
    (l' : a' ≅ b') (m' : b' ≅ d') (r' : a' ≅ c') (s' : c' ≅ d')
    (h : l ≪≫ m = r ≪≫ s) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (hl : HEq l' l) (hm : HEq m' m) (hr : HEq r' r) (hs : HEq s' s) :
    l' ≪≫ m' = r' ≪≫ s' := by
  subst a' b' c' d'
  cases eq_of_heq hl
  cases eq_of_heq hm
  cases eq_of_heq hr
  cases eq_of_heq hs
  exact h

end SerrePositivity.InfinityCategories.F2
