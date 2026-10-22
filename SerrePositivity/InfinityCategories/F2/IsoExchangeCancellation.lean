module

public import Mathlib.CategoryTheory.Iso

/-!
概要：元の四つの指定同型の交換式から、外側の指定同型を逆との合成で消去する。
方針：同じ二つの逆を合成し、同型の単位則を使う。
規約：指定された四因子を保持。使われ方：上側単位因子の消去の厳密な式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定正方形の交換式は、両側の指定因子を逆へ移した等式を与える。 -/
lemma iso_inverse_exchange_of_square {C : Type u} [Category.{v} C] {a b c d : C}
    (e : a ≅ b) (f : b ≅ d) (g : a ≅ c) (h : c ≅ d)
    (q : e ≪≫ f = g ≪≫ h) : g.symm ≪≫ e = h ≪≫ f.symm := by
  calc
    _ = g.symm ≪≫ (e ≪≫ f) ≪≫ f.symm := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = g.symm ≪≫ (g ≪≫ h) ≪≫ f.symm := congrArg (fun i => g.symm ≪≫ i ≪≫ f.symm) q
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
