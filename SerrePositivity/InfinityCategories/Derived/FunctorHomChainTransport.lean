module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
/-!
概要：端点を揃えた全関手射の三段経路を、同じ比較等式へ移す。
方針：一般の射と端点の等式の下で二度の合成輸送をまとめる。
規約：指定射の異種等式を保持する。使われ方：導来 kernel 合成子の共通経路比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 同じ指定射の比較を保った三段経路の端点輸送は、元の経路等式を反映する。 -/
lemma functorHom_chain_eq_of_heq {X Y : SSet.{u}}
    {f g h k t g' h' k' : X ⟶ Y}
    (c : FunctorHom f t) (r : FunctorHom t k) (r' : FunctorHom t k')
    (q : FunctorHom f g) (q' : FunctorHom f g')
    (d : FunctorHom g h) (d' : FunctorHom g' h')
    (a : FunctorHom h k) (a' : FunctorHom h' k')
    (hg : g = g') (hh : h = h') (hk : k = k')
    (hr : HEq r r') (hq : HEq q q') (hd : HEq d d') (ha : HEq a a')
    (he : c ≫ r' = q' ≫ d' ≫ a') : c ≫ r = q ≫ d ≫ a := by
  have hL := functorHom_comp_heq c r c r' rfl rfl hk (HEq.refl _) hr
  have hM := functorHom_comp_heq d a d' a' hg hh hk hd ha
  have hR := functorHom_comp_heq q (d ≫ a) q' (d' ≫ a') rfl hg hk hq hM
  exact eq_of_heq (hL.trans ((heq_of_eq he).trans hR.symm))
end SerrePositivity.InfinityCategories
