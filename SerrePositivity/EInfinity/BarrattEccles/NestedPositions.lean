module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues

/-!
# 入れ子の二段の挿入の位置の比較

概要：Berger–Fresse §0.10 の入れ子の部分合成で、二つの挿入順序による入力位置を比較する。
方針：外側の残り・中間の残り・最内層の三種類を挿入分解で表す。
規約：最終 arity の括弧の違いは加法の結合則の Fin.cast で移す。
使われ方：置換の入れ子結合則の各入力の比較に用いる。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：外側の位置 i の内側の位置 j が一回目の挿入後に持つ位置（Berger–Fresse §0.10）。
方針：一回目の挿入区間の内側の位置として指定する。
規約：値は i+j、arity は m+n+1 である。
使われ方：入れ子の二回目の挿入位置を指定する。 -/
def nestedSlot (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) : Fin (m + n + 1) :=
  insertedPosition m (n + 1) i j

/-- 概要：元の外側の残りの入力は一回目の挿入後にも二回目の指定位置と異なる（Berger–Fresse §0.10）。
方針：残りの入力と挿入区間の入力が異なることを使う。
規約：二回目の挿入位置は i+j である。
使われ方：外側の残りの入力に二回目の remainingPosition を適用する。 -/
def nestedOuterRemaining (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : {a : Fin (m + 1) // a ≠ i}) : {b : Fin (m + n + 1) // b ≠ nestedSlot m n i j} :=
  ⟨remainingPosition m (n + 1) i a, remainingPosition_ne_inserted m (n + 1) i a j⟩

/-- 概要：内側の残りの入力は一回目の挿入後にも二回目の指定位置と異なる（Berger–Fresse §0.10）。
方針：挿入区間の位置の値の単射性を使う。
規約：a は内側の指定位置 j と異なる。
使われ方：中間の入力へ二回目の remainingPosition を適用する。 -/
def nestedInnerRemaining (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : {a : Fin (n + 1) // a ≠ j}) : {b : Fin (m + n + 1) // b ≠ nestedSlot m n i j} :=
  ⟨insertedPosition m (n + 1) i a.val, by
    intro h
    have hv := congrArg Fin.val h
    change i.val + a.val.val = i.val + j.val at hv
    exact a.property (Fin.ext (by omega))⟩

/-- 概要：外側の残りの入力の位置は二つの入れ子の挿入順序で一致する（Berger–Fresse §0.10）。
方針：位置の値を remainingValue の二段の式へ直して数値の結合則を使う。
規約：左括弧の最終 arity を右括弧の最終 arity へ移送する。
使われ方：置換の入れ子結合則の外側の入力を比較する。 -/
lemma nestedPosition_outer (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : {a : Fin (m + 1) // a ≠ i}) :
    Fin.cast (Nat.add_assoc m n k)
        (remainingPosition (m + n) k (nestedSlot m n i j) (nestedOuterRemaining m n i j a)) =
      remainingPosition m (n + k) i a := by
  apply Fin.ext
  simp only [Fin.val_cast, remainingPosition_val, nestedSlot, insertedPosition_val,
    nestedOuterRemaining]
  exact remainingValue_nested_outer n k i.val j.val a.val.val
    (Nat.le_of_lt_succ j.isLt) (fun h => a.property (Fin.ext h))

/-- 概要：中間の残りの入力の位置は二つの入れ子の挿入順序で一致する（Berger–Fresse §0.10）。
方針：内側の remainingValue の式を外側の位置 i で平行移動する。
規約：内側の挿入区間の出力位置を外側の挿入区間へ入れる。
使われ方：置換の入れ子結合則の中間の入力を比較する。 -/
lemma nestedPosition_inner (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : {a : Fin (n + 1) // a ≠ j}) :
    Fin.cast (Nat.add_assoc m n k)
        (remainingPosition (m + n) k (nestedSlot m n i j) (nestedInnerRemaining m n i j a)) =
      insertedPosition m (n + k) i (remainingPosition n k j a) := by
  apply Fin.ext
  simp only [Fin.val_cast, remainingPosition_val, nestedSlot, insertedPosition_val,
    nestedInnerRemaining]
  exact remainingValue_nested_inner k i.val j.val a.val.val
    (fun h => a.property (Fin.ext h))

/-- 概要：最内層の入力の位置は二つの入れ子の挿入順序で一致する（Berger–Fresse §0.10）。
方針：挿入区間の位置を値の和へ直して加法の結合則を使う。
規約：最内層の arity k が0の場合は入力が存在しない。
使われ方：置換の入れ子結合則の最内層の入力を比較する。 -/
lemma nestedPosition_inside (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) (a : Fin k) :
    Fin.cast (Nat.add_assoc m n k) (insertedPosition (m + n) k (nestedSlot m n i j) a) =
      insertedPosition m (n + k) i (insertedPosition n k j a) := by
  apply Fin.ext
  simp only [Fin.val_cast, nestedSlot, insertedPosition_val]
  exact Nat.add_assoc _ _ _

end SerrePositivity.EInfinity.BarrattEccles
