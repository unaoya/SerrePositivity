module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePath

/-!
# shuffle の二つの単体写像の全射性

概要：格子路の座標は最初から最後まで全ての中間整数値を通る。
方針：指定値以上となる最初の頂点を取り、一歩の増加が高々1であることを使う。
規約：KST Construction A.5 の標準 shuffle。
使われ方：二つの単体写像が退化方向の全射であることと正規化への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open scoped Simplicial

/-- 概要：零から p まで一歩で高々1だけ増える有限の整数値の路は中間値を全て取る。
方針：指定値以上となる最小の頂点と、その直前の値を比較する。
規約：KST A.5 の格子路の一般補題。単調性自体は不要。
使われ方：shuffle の二つの座標の全射性。 -/
lemma discretePath_intermediate {n p : ℕ} (f : Fin (n + 1) → ℕ)
    (h₀ : f 0 = 0) (h₁ : f (Fin.last n) = p)
    (hs : ∀ x : Fin n, f x.succ ≤ f x.castSucc + 1)
    (j : ℕ) (hj : j ≤ p) : ∃ x, f x = j := by
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun x ↦ j ≤ f x)
  have hS : S.Nonempty := by
    refine ⟨Fin.last n, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, h₁]
    exact hj
  let x := S.min' hS
  have hx : j ≤ f x := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  by_cases hx₀ : x = 0
  · refine ⟨x, ?_⟩
    rw [hx₀, h₀] at hx ⊢
    omega
  · have hxpos : 0 < (x : ℕ) := by
      by_contra! h
      apply hx₀
      exact Fin.ext (Nat.eq_zero_of_le_zero h)
    let y : Fin n := ⟨(x : ℕ) - 1, by have := x.isLt; omega⟩
    have hy : y.succ = x := by
      apply Fin.ext
      change (x : ℕ) - 1 + 1 = (x : ℕ)
      omega
    have hlt : y.castSucc < x := by
      change (x : ℕ) - 1 < (x : ℕ)
      omega
    have hp : f y.castSucc < j := by
      by_contra! hp
      have hymem : y.castSucc ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hp
      have hmin : x ≤ y.castSucc := Finset.min'_le S _ hymem
      exact (not_le_of_gt hlt) hmin
    have hstep := hs y
    rw [hy] at hstep
    exact ⟨x, by omega⟩

/-- 概要：shuffle の第一写像は全射。
方針：始点零、終点 p、一歩の増加が0または1であることを使う。
規約：KST A.5、水平ステップの座標。
使われ方：第一因子に適用する写像が単体的な退化方向にあることの確認。 -/
lemma ShuffleIndex.left_surjective {p n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex p n) :
    Function.Surjective s.left.toOrderHom := by
  intro j
  obtain ⟨x, hx⟩ := discretePath_intermediate (fun x ↦ (s.left.toOrderHom x : ℕ))
    s.left_zero s.left_last (fun x ↦ by
      rw [s.left_step]
      split_ifs <;> omega) j (Nat.le_of_lt_succ j.isLt)
  exact ⟨x, Fin.ext hx⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex export _root_.SerrePositivity.KST.ProExcision.ShuffleIndex (left_surjective)

/-- 概要：shuffle の第二写像は全射。
方針：始点零、終点 q、一歩の増加が0または1であることを使う。
規約：KST A.5、垂直ステップの座標。
使われ方：第二因子に適用する写像が単体的な退化方向にあることの確認。 -/
lemma ShuffleIndex.right_surjective {p q n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex p n) (h : p + q = n) :
    Function.Surjective (s.right h).toOrderHom := by
  intro j
  obtain ⟨x, hx⟩ := discretePath_intermediate (fun x ↦ ((s.right h).toOrderHom x : ℕ))
    (s.right_zero h) (s.right_last h) (fun x ↦ by
      rw [s.right_step h]
      split_ifs <;> omega) j (Nat.le_of_lt_succ j.isLt)
  exact ⟨x, Fin.ext hx⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex export _root_.SerrePositivity.KST.ProExcision.ShuffleIndex (right_surjective)

end SerrePositivity.KST.ProExcision
