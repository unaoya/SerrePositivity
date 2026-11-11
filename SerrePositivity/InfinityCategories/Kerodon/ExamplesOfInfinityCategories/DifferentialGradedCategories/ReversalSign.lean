module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumFlagAscending

/-!
# 降順と昇順の旗の反転符号

概要：Fin m の順序反転の置換符号は degreeSign m に等しい。
方針：置換の符号を反転対の積で計算し、全ての二要素の組が反転することを使う。
規約：整数に値を取る符号として標準 DK 座標の符号と比較する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の唯一の昇順の旗の係数の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped BigOperators

private lemma sign_eq_signAux {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  refine Equiv.Perm.swap_induction_on
    (motive := fun τ : Equiv.Perm (Fin m) ↦ Equiv.Perm.sign τ = Equiv.Perm.signAux τ) σ ?_ ?_
  · simp
  · intro f x y hxy ih
    rw [Equiv.Perm.sign_mul, Equiv.Perm.signAux_mul,
      Equiv.Perm.sign_swap hxy, Equiv.Perm.signAux_swap hxy, ih]

/-- 概要：Fin m の順序付きの小さい二要素の組の数は二項係数である。
方針：各最大元 k ごとの k 個の選択を足し、二項係数の漸化式を使う。
規約：Mathlib の置換符号の反転対の集合をそのまま数える。
使われ方：Kerodon 2.5.9（Tag 00SC） の反転の置換符号の指数。 -/
lemma finPairsLT_card (m : ℕ) : (Equiv.Perm.finPairsLT m).card = m.choose 2 := by
  simp only [Equiv.Perm.finPairsLT, Finset.card_sigma, Finset.card_attachFin, Finset.card_range]
  rw [← Finset.sum_range (fun j : ℕ ↦ j)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    exact Nat.add_comm _ _

/-- 概要：順序反転の整数の置換符号は標準座標への次数符号に等しい。
方針：全ての反転対が −1 を与えるので、その積を二項係数のべきにする。
規約：零個・一個の座標でも符号は +1。
使われ方：HA 1.3.1.17 の立方体評価と標準 DK 成分の二つの符号の相殺。 -/
lemma revPerm_sign (m : ℕ) : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ℤ) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign m := by
  rw [sign_eq_signAux]
  have h : Equiv.Perm.signAux (Fin.revPerm : Equiv.Perm (Fin m)) =
      (-1 : ℤˣ) ^ m.choose 2 := by
    unfold Equiv.Perm.signAux
    calc
      _ = ∏ _ ∈ Equiv.Perm.finPairsLT m, (-1 : ℤˣ) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact ite_eq_left (Fin.rev_strictAnti (Equiv.Perm.mem_finPairsLT.mp hp)).le
      _ = _ := by rw [Finset.prod_const, finPairsLT_card]
  rw [h]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
