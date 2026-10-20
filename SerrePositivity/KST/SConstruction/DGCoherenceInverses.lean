module
public import Mathlib.CategoryTheory.Iso

/-! # 同型の五角と自然性を逆向きの経路へ移す
概要：順向きの経路の等号から、同じ同型の逆射の経路を比較する。
方針：同型の外延性と圏の打ち消しを抽象的な圏で使う。
規約：具体的な双加群射を展開しない。使われ方：実延長の三重比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- 二つと三つの同型による経路の等号は、その逆経路の等号を与える。 -/
lemma dgIso_inverse_pentagon {X Y Z W V : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W) (d : V ≅ W) (e : X ≅ V)
    (h : d.inv ≫ e.inv = c.inv ≫ b.inv ≫ a.inv) :
    a.hom ≫ b.hom ≫ c.hom = e.hom ≫ d.hom := by
  have hi : d.symm ≪≫ e.symm = c.symm ≪≫ b.symm ≪≫ a.symm := Iso.ext h
  have ht := congrArg (fun k => k.inv) hi
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using ht.symm

/-- 同型の順方向の自然性四角形は、同じ逆射の四角形を与える。 -/
lemma dgIso_inverse_naturality {X Y X' Y' : C} (a : X ≅ Y) (b : X' ≅ Y')
    (u : X ⟶ X') (v : Y ⟶ Y') (h : u ≫ b.hom = a.hom ≫ v) :
    v ≫ b.inv = a.inv ≫ u := by
  apply (cancel_epi a.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- 同型の順射で始まる元の経路の等号を、同じ逆射で解く。 -/
lemma dgIso_move_hom_left {X Y Z : C} (a : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (h : g = a.hom ≫ f) : f = a.inv ≫ g := by
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.SConstruction
