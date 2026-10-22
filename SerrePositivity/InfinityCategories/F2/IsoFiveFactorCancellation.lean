module

public import Mathlib.CategoryTheory.Iso

/-!
概要：元の五因子の指定整合式から、右辺の先頭の同型をその逆で消去する。
方針：同じ整合式に左から元の逆同型を合成する。
規約：指定された五同型を保持。使われ方：全族の単位三角柱の外側因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 元の五因子の関係の右辺の先頭因子は、その同じ逆を左合成して消去できる。 -/
lemma iso_five_factor_cancel_prefix {C : Type u} [Category.{v} C] {x y z w t : C}
    (a : x ≅ y) (b : y ≅ z) (c : x ≅ w) (d : w ≅ t) (e : t ≅ z)
    (h : a ≪≫ b = c ≪≫ d ≪≫ e) :
    (c.symm ≪≫ a) ≪≫ b = d ≪≫ e := by
  calc
    _ = c.symm ≪≫ (a ≪≫ b) := Iso.trans_assoc _ _ _
    _ = c.symm ≪≫ (c ≪≫ d ≪≫ e) := congrArg (fun f => c.symm ≪≫ f) h
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- 同じ指定自然性正方形を、元の二つの縦比較による共役として解く。 -/
lemma iso_conjugation_of_naturality {C : Type u} [Category.{v} C] {x y z w : C}
    (n : x ≅ y) (a : x ≅ z) (b : y ≅ w) (m : z ≅ w)
    (h : n ≪≫ b = a ≪≫ m) : (a.symm ≪≫ n) ≪≫ b = m := by
  calc
    _ = a.symm ≪≫ (n ≪≫ b) := Iso.trans_assoc _ _ _
    _ = a.symm ≪≫ (a ≪≫ m) := congrArg (fun e => a.symm ≪≫ e) h
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
