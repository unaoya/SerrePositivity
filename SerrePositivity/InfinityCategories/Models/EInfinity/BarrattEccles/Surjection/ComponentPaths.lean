module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePaths
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
模型。文献の定義との比較は後で
# 全成分の次数による格子経路と符号

概要：Berger–Fresse §1.5.4–6 の内側・外側成分の交互の移動を連結する。
方針：内側と次の外側の次数の対のリストで帰納する。
規約：対の第一成分は垂直、第二成分は水平。
使われ方：合成語の分割次数からの具体的な候補経路を与える。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：成分次数の対の列から実際の shuffle 経路を構成（BF §1.5.4）。
方針：各対を垂直から水平へ進む経路にし、先頭から連結する。
規約：両座標の総次数はそれぞれの成分の総和。
使われ方：外側の最初の成分の後の全ての移動を与える。 -/
def blocks : (xs : List (ℕ × ℕ)) → ShufflePath (xs.map Prod.snd).sum (xs.map Prod.fst).sum
  | [] => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal 0
  | (v, h) :: xs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner h v) (blocks xs)

/-- 概要：成分経路の全ての垂直先行・水平後行の交換次数（BF §1.5.6）。
方針：先頭垂直次数と全後続水平次数の積を再帰的に足す。
規約：先頭と同じ対の水平次数も通過する。
使われ方：成分経路の shuffle 符号を整数指数で計算する。 -/
def blockExponent : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (v, h) :: xs => blockExponent xs + v * (h + (xs.map Prod.snd).sum)

/-- 概要：全成分を連結した経路の符号は定義した交換次数の冪（BF §1.5.6）。
方針：各成分経路と連結の符号を帰納法で掛け合わせる。
規約：実際の shuffle 置換の signature の等式。
使われ方：合成語の Koszul 符号との比較の経路側の式。 -/
lemma blocks_sign (xs : List (ℕ × ℕ)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks xs).sign = (-1 : ℤˣ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent xs := by
  induction xs with
  | nil => exact ShufflePath.sign_rightZero (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal 0)
  | cons p xs ih =>
    rcases p with ⟨v, h⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_sign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner_sign, ih]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent, Nat.mul_add, pow_add]
    ac_rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath
