module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitAt
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 二つの入力ブロックの arity の和

概要：Berger–Moerdijk §1 の部分合成則で二つの連続した入力ブロックの総 arity を比較する。
方針：後半の長さで帰納し、有限和を最後の因子で分ける。
規約：前半の添字は castAdd、後半の添字は natAdd を使う。
使われ方：ブロックごとの反復合成の出力を全入力の arity へ移す。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open scoped _root_.BigOperators

/-- 概要：有限入力族の総 arity は前半と後半の arity の和となる（Berger–Moerdijk §1）。
方針：後半の末尾の項を分け、残りへ帰納仮定を適用する。
規約：零長の前半と後半の両方を許す。
使われ方：入力族の二部分へのテンソル分離に伴う出力の長さを指定する。 -/
lemma tensorFamily_sum_splitAt (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (∑ j, s j) = (∑ j : Fin n, s (j.castAdd m)) + (∑ j : Fin m, s (j.natAdd n)) := by
  induction m with
  | zero =>
    simp only [Fin.sum_univ_zero, Nat.add_zero]
    rfl
  | succ m ih =>
    erw [Fin.sum_univ_castSucc s,
      Fin.sum_univ_castSucc (fun j : Fin (m + 1) => s (j.natAdd n))]
    have h := congrArg (· + s (Fin.last (n + m))) (ih (fun j => s j.castSucc))
    simp only [Nat.add_assoc] at h
    exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
