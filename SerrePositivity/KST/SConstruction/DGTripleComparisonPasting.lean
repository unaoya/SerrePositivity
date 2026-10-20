module
public import Mathlib.CategoryTheory.Functor.Basic

/-! # 三重比較の自然性と五角を抽象的な圏で貼り合わせる
概要：graph の結合則を関手で運び、元の二つの三重比較経路を照合する。
方針：二つの自然性四角形と五角の等号を、抽象的な射のまま合成する。
規約：具体的な coend 射を簡約しない。使われ方：実延長の三重 tensor 比較。
-/
@[expose] public section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {A : Type u} [Category.{v} A] {B : Type w} [Category.{z} B]

/-- 同じ graph 射・比較射・自然性と五角による、三重比較の二経路の一致。 -/
lemma dgTripleComparison_pasting (K : A ⥤ B) {X0 X1 X2 X3 X4 X5 : A}
    (u : X0 ⟶ X1) (v : X1 ⟶ X2) (e : X2 ⟶ X5)
    (a : X0 ⟶ X3) (w : X3 ⟶ X4) (z : X4 ⟶ X5)
    {S0 S1 S2 S3 S4 : B}
    (i0 : S0 ⟶ S1) (i1 : S1 ⟶ S2) (b : S2 ⟶ K.obj X1) (c : S1 ⟶ K.obj X0)
    (d : S0 ⟶ S3) (j : S3 ⟶ K.obj X3) (k : S3 ⟶ S4) (l : S4 ⟶ K.obj X4)
    (r : S0 ⟶ S2) (c1 : S2 ⟶ K.obj X2) (c2 : S4 ⟶ K.obj X5)
    (hr : r = i0 ≫ i1) (hc1 : c1 = b ≫ K.map v) (hc2 : c2 = l ≫ K.map z)
    (hg : u ≫ v ≫ e = a ≫ w ≫ z) (hn1 : i1 ≫ b = c ≫ K.map u)
    (hp : i0 ≫ c ≫ K.map a = d ≫ j) (hn2 : j ≫ K.map w = k ≫ l) :
    r ≫ c1 ≫ K.map e = d ≫ k ≫ c2 := by
  calc
    r ≫ c1 ≫ K.map e = i0 ≫ i1 ≫ b ≫ K.map v ≫ K.map e := by
      rw [hr, hc1]
      simp only [Category.assoc]
    _ = i0 ≫ c ≫ K.map u ≫ K.map v ≫ K.map e := by
      have h := congrArg (fun f => i0 ≫ f ≫ K.map v ≫ K.map e) hn1
      simpa only [Category.assoc] using h
    _ = i0 ≫ c ≫ K.map (u ≫ v ≫ e) := by
      simp only [Functor.map_comp]
    _ = i0 ≫ c ≫ K.map (a ≫ w ≫ z) := congrArg (fun f => i0 ≫ c ≫ K.map f) hg
    _ = i0 ≫ c ≫ K.map a ≫ K.map w ≫ K.map z := by
      simp only [Functor.map_comp]
    _ = d ≫ j ≫ K.map w ≫ K.map z := by
      have h := congrArg (fun f => f ≫ K.map w ≫ K.map z) hp
      simpa only [Category.assoc] using h
    _ = d ≫ k ≫ l ≫ K.map z := by
      have h := congrArg (fun f => d ≫ f ≫ K.map z) hn2
      simpa only [Category.assoc] using h
    _ = d ≫ k ≫ c2 := by rw [hc2]

end SerrePositivity.KST.SConstruction
