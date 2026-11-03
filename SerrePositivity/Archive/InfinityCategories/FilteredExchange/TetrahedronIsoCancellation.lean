module

public import Mathlib.CategoryTheory.Iso

/-!
概要：四面の貼り合わせと元の始点正方形から、二通りの合成を一致させる。
方針：同じ実共有辺の比較を同型の結合則と逆の消去で消す。
規約：高次整合を仮定で追加しない。使われ方：実四面体の指定輸送比較。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 四面の実辺貼り合わせ式と始点自然性の正方形による同型の消去。 -/
lemma tetrahedronIsoCancellation {C : Type u} [Category.{v} C]
    {A B X Z E F Y D : C} (e : A ≅ B) (u : X ≅ A) (v : Z ≅ X)
    (w : X ≅ Y) (r : Z ≅ E) (t : E ≅ F) (z : Z ≅ D)
    (a : B ≅ Y) (b : Y ≅ D) (c : A ≅ E) (d : F ≅ D) (c' : B ≅ F)
    (ha : a = (u ≪≫ e).symm ≪≫ w) (hb : b = (v ≪≫ w).symm ≪≫ z)
    (hc : c = (v ≪≫ u).symm ≪≫ r) (hd : d = (r ≪≫ t).symm ≪≫ z)
    (hn : e ≪≫ c' = c ≪≫ t) : a ≪≫ b = c' ≪≫ d := by
  have h : c' = e.symm ≪≫ c ≪≫ t := by
    have h := congrArg (fun q => e.symm ≪≫ q) hn
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using h
  rw [ha, hb, hd, h, hc]
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]

end SerrePositivity.InfinityCategories.F2
