module

public import SerrePositivity.EInfinity.BarrattEccles.ParallelPositions

/-!
# 並列の二回目の挿入へ移した置換の値

概要：Berger–Fresse §0.10 の最初の部分合成の出力置換を二回目の外側 arity に移す。
方針：Fin の長さの等式による共役を使い、残りの入力と挿入区間で値を計算する。
規約：最初の出力 arity m+1+n を m+n+1 として扱う。
使われ方：置換の並列結合則の二回目の部分合成の値を計算する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：一回目の部分合成の置換を次の外側 arity へ移す（Berger–Fresse §0.10）。
方針：arity の加法の括弧を Fin の同値による共役で直す。
規約：元の外側 arity は m+2 である。
使われ方：異なる入力への二回の部分合成を型付けする。 -/
def permutationAfterInsertion (m n : ℕ) (i : Fin (m + 2))
    (σ : Equiv.Perm (Fin (m + 2))) (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (m + n + 1)) :=
  (finCongr (by omega : m + 1 + n = m + n + 1)).permCongr
    (permutationComposition (m + 1) n i σ τ)

/-- 概要：次数を移した一回目の置換は残りの入力を通常の番号の公式で動かす（Berger–Fresse §0.10）。
方針：共役の次数移送を消去して部分合成の残りの入力の公式を使う。
規約：a は最初の指定位置 i と異なる。
使われ方：二回目の指定位置と外側の残りの入力の像を計算する。 -/
lemma permutationAfterInsertion_remaining (m n : ℕ) (i : Fin (m + 2))
    (σ : Equiv.Perm (Fin (m + 2))) (τ : Equiv.Perm (Fin n))
    (a : {a : Fin (m + 2) // a ≠ i}) :
    (permutationAfterInsertion m n i σ τ
      (Fin.cast (by omega : m + 1 + n = m + n + 1) (remainingPosition (m + 1) n i a))).val =
        remainingValue n (σ i).val (σ a.val).val := by
  change (permutationComposition (m + 1) n i σ τ (remainingPosition (m + 1) n i a)).val = _
  exact permutationComposition_remaining_val (m + 1) n i σ τ a

/-- 概要：次数を移した一回目の置換の挿入区間の値（Berger–Fresse §0.10）。
方針：共役の次数移送を消去して部分合成の挿入区間の公式を使う。
規約：入力 i+a の像の値は σ(i)+τ(a) である。
使われ方：並列結合則の一方の挿入区間の入力を比較する。 -/
lemma permutationAfterInsertion_inside (m n : ℕ) (i : Fin (m + 2))
    (σ : Equiv.Perm (Fin (m + 2))) (τ : Equiv.Perm (Fin n)) (a : Fin n) :
    (permutationAfterInsertion m n i σ τ
      (Fin.cast (by omega : m + 1 + n = m + n + 1) (insertedPosition (m + 1) n i a))).val =
        (σ i).val + (τ a).val := by
  change (permutationComposition (m + 1) n i σ τ (insertedPosition (m + 1) n i a)).val = _
  exact congrArg Fin.val (permutationComposition_inside (m + 1) n i σ τ a)

/-- 概要：一回目の置換が二回目の指定位置へ送る値（Berger–Fresse §0.10）。
方針：残りの入力の値の公式を元の二つ目の指定位置へ適用する。
規約：二つの指定位置 i,j は異なる。
使われ方：二回目の部分合成の出力の挿入位置を計算する。 -/
lemma permutationAfterInsertion_slot (m n : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin (m + 2))) (τ : Equiv.Perm (Fin n)) :
    (permutationAfterInsertion m n i σ τ (parallelSlot m n i j hji)).val =
      remainingValue n (σ i).val (σ j).val :=
  permutationAfterInsertion_remaining m n i σ τ ⟨j, hji⟩

end SerrePositivity.EInfinity.BarrattEccles
