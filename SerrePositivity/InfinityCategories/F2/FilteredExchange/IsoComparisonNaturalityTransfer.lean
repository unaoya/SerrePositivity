module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IsoExchangeCancellation

/-!
概要：同じ全 Hom の自然性を、指定された両端比較で移した作用比較へ移す。
方針：二つの指定正方形を合成し、同じ二つの逆同型を使う。
規約：元の全比較を保持。使われ方：native な作用比較の指定自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 元の自然性正方形と元の両端比較の正方形は、同じ作用比較の自然性を与える。 -/
lemma iso_comparison_naturality_transfer {C : Type u} [Category.{v} C]
    {a b c d e f : C} (n : a ≅ b) (v : c ≅ d) (tx : a ≅ c) (ty : b ≅ d)
    (ux : a ≅ e) (uy : b ≅ f) (m : e ≅ f)
    (ht : n ≪≫ ty = tx ≪≫ v) (hu : ux ≪≫ m = n ≪≫ uy) :
    (tx.symm ≪≫ ux) ≪≫ m = v ≪≫ (ty.symm ≪≫ uy) := by
  calc
    _ = tx.symm ≪≫ (ux ≪≫ m) := Iso.trans_assoc _ _ _
    _ = tx.symm ≪≫ (n ≪≫ uy) := congrArg (fun k => tx.symm ≪≫ k) hu
    _ = (tx.symm ≪≫ n) ≪≫ uy := (Iso.trans_assoc _ _ _).symm
    _ = (v ≪≫ ty.symm) ≪≫ uy := congrArg (fun k => k ≪≫ uy)
      (iso_inverse_exchange_of_square n ty tx v ht)
    _ = _ := Iso.trans_assoc _ _ _

end SerrePositivity.InfinityCategories.F2
