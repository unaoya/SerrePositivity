module

public import Mathlib.CategoryTheory.Iso

/-!
概要：同じ共有辺を持つ二つの指定可換正方形を右へ貼り合わせる。
方針：指定等式を同じ同型へ合成し、結合律で揃える。
規約：指定値を保持。使われ方：全 Hom の native 比較と普遍輸送成分の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ共有辺を持つ二正方形の貼り合わせは、元の指定六辺の合成と整合する。 -/
lemma iso_square_paste_right {C : Type u} [Category.{v} C] {a b c d e f : C}
    (m : a ≅ b) (ax : a ≅ c) (by₀ : b ≅ d) (n : c ≅ d)
    (ux : c ≅ e) (uy : d ≅ f) (n' : e ≅ f)
    (h : m ≪≫ by₀ = ax ≪≫ n) (ht : n ≪≫ uy = ux ≪≫ n') :
    m ≪≫ by₀ ≪≫ uy = ax ≪≫ ux ≪≫ n' := by
  calc
    _ = (m ≪≫ by₀) ≪≫ uy := (Iso.trans_assoc _ _ _).symm
    _ = (ax ≪≫ n) ≪≫ uy := congrArg (fun k => k ≪≫ uy) h
    _ = ax ≪≫ (n ≪≫ uy) := Iso.trans_assoc _ _ _
    _ = _ := congrArg (fun k => ax ≪≫ k) ht

/-- 元の正方形を右へ合成し、同じ指定二因子の消去式を代入する。 -/
lemma iso_square_finish_right {C : Type u} [Category.{v} C] {a b c d e : C}
    (f : a ≅ b) (g : b ≅ d) (h : a ≅ c) (i : c ≅ d) (k : d ≅ e) (j : c ≅ e)
    (hs : f ≪≫ g = h ≪≫ i) (hi : i ≪≫ k = j) : f ≪≫ g ≪≫ k = h ≪≫ j := by
  calc
    _ = (f ≪≫ g) ≪≫ k := (Iso.trans_assoc _ _ _).symm
    _ = (h ≪≫ i) ≪≫ k := congrArg (fun v => v ≪≫ k) hs
    _ = h ≪≫ (i ≪≫ k) := Iso.trans_assoc _ _ _
    _ = _ := congrArg (fun v => h ≪≫ v) hi

end SerrePositivity.InfinityCategories.F2
