module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyBlockSum

/-!
模型。文献の定義との比較は後で
# 先頭ブロックを一入力へまとめる arity 族

概要：Berger–Moerdijk §1 の全合成の結合則で用いる入力族を定める。
方針：先頭 n 入力の arity の和を新しい先頭に置き、後半 m 入力をそのまま保つ。
規約：新しい入力集合は Fin (1+m)、元の入力集合は Fin (n+m)。
使われ方：内側の全合成の結果を外側の先頭入力へ代入する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open scoped _root_.BigOperators

/-- 概要：先頭ブロックを一入力へまとめた arity 族（Berger–Moerdijk §1）。
方針：Fin.addCases で先頭の和と後半の族を連結する。
規約：空の先頭ブロックの和も零として許す。
使われ方：全合成の結合則の外側の入力族となる。 -/
def firstBlockArities (n m : ℕ) (s : Fin (n + m) → ℕ) : Fin (1 + m) → ℕ :=
  Fin.addCases (fun _ : Fin 1 => ∑ j : Fin n, s (j.castAdd m))
    (fun j => s (j.natAdd n))

/-- 概要：まとめた入力族の先頭は元の前半の和である（Berger–Moerdijk §1）。
方針：Fin.addCases の左側で評価する。
規約：先頭は Fin 1 の零の castAdd で表す。
使われ方：先頭への部分合成の arity を同定する。 -/
@[simp]
lemma firstBlockArities_head (n m : ℕ) (s : Fin (n + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s ((0 : Fin 1).castAdd m) = ∑ j : Fin n, s (j.castAdd m) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities, Fin.addCases_left]

/-- 概要：まとめた入力族の後半は元の後半に一致する（Berger–Moerdijk §1）。
方針：Fin.addCases の右側で評価する。
規約：natAdd 1 と natAdd n でそれぞれの後半を埋め込む。
使われ方：後半の演算族へのテンソル代入を同定する。 -/
@[simp]
lemma firstBlockArities_tail (n m : ℕ) (s : Fin (n + m) → ℕ) (j : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s (j.natAdd 1) = s (j.natAdd n) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities, Fin.addCases_right]

/-- 概要：先頭ブロックをまとめても arity の総和は変わらない（Berger–Moerdijk §1）。
方針：二ブロックへの和の分解と一入力の和の計算を使う。
規約：空の前半と後半を含む全ての長さに適用する。
使われ方：二通りの全合成の終域の arity を同定する。 -/
lemma firstBlockArities_sum (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (∑ j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j) = ∑ j, s j := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt 1 m]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
