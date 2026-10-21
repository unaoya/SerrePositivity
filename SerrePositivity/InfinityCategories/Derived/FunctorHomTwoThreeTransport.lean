module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
/-!
概要：全関手射の二辺経路と三辺経路を、同じ指定射の端点輸送で照合する。
方針：型付きの異種等式を各合成へ移してから、元の等式へ戻す。
規約：元の経路の値を保つ。使われ方：通常 kernel の五角経路。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 明示した全端点と指定射の輸送の下で、二辺と三辺の経路等式を反映する。 -/
lemma functorHom_two_three_eq_of_heq {X Y : SSet.{u}}
    {f g h t k f' g' h' t' k' : X ⟶ Y}
    (c : FunctorHom f g) (r : FunctorHom g k)
    (q : FunctorHom f h) (d : FunctorHom h t) (a : FunctorHom t k)
    (c' : FunctorHom f' g') (r' : FunctorHom g' k')
    (q' : FunctorHom f' h') (d' : FunctorHom h' t') (a' : FunctorHom t' k')
    (hf : f = f') (hg : g = g') (hh : h = h') (ht : t = t') (hk : k = k')
    (hc : HEq c c') (hr : HEq r r') (hq : HEq q q') (hd : HEq d d') (ha : HEq a a')
    (he : c' ≫ r' = q' ≫ d' ≫ a') : c ≫ r = q ≫ d ≫ a := by
  have hL := functorHom_comp_heq c r c' r' hf hg hk hc hr
  have hM := functorHom_comp_heq d a d' a' hh ht hk hd ha
  have hR := functorHom_comp_heq q (d ≫ a) q' (d' ≫ a') hf hh hk hq hM
  exact eq_of_heq (hL.trans ((heq_of_eq he).trans hR.symm))
end SerrePositivity.InfinityCategories
