module

public import Mathlib.Data.Fin.Basic

/-!
模型。文献の定義との比較は後で
# 元の有限辺の全比較による端点の一致

Berger–Fresse §2.2.6、M14 L12a の端点の復元の補助。
同じ幅以下の二端点を、元の有限辺との比較によって読む。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C448：元の有限辺との全比較が同じなら端点も同じ（BF §2.2.6 の有限比較の補助）。 -/
lemma nat_eq_of_fin_le_iff {m : ℕ} (x y : ℕ) (hx : x ≤ m) (hy : y ≤ m)
    (h : ∀ a : Fin m, x ≤ a.val ↔ y ≤ a.val) : x = y := by
  apply Nat.le_antisymm
  · by_contra hnot
    let a : Fin m := ⟨y, by omega⟩
    have he := (h a).mpr (show y ≤ a.val from Nat.le_refl y)
    change x ≤ y at he
    omega
  · by_contra hnot
    let a : Fin m := ⟨x, by omega⟩
    have he := (h a).mp (show x ≤ a.val from Nat.le_refl x)
    change y ≤ x at he
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
