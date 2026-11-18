module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution
public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 代入ラベルの単射性と内外の隣接境界

概要：Berger–Fresse §1.2.4 の合成で異なるラベルが隣接重複にならないことを示す。
方針：BE の入力ラベル直和分解の単射性と内外の非交差を使う。
規約：外側 arity m+1、内側 n。
使われ方：正の内側語を代入した合成語の非退化性を検証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：挿入ラベルは元の内側ラベルを区別する（BF §1.2.4）。
方針：入力ラベル直和分解の逆の単射性を使う。
規約：内側 arity 零も含む。
使われ方：内側部分語の隣接非一致を保つ。 -/
lemma insertedPosition_injective (m n : ℕ) (k : Fin (m + 1)) :
    Function.Injective (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) := by
  intro a b he
  exact Sum.inr.inj ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.injective he)

/-- 概要：残りの外側ラベルは元の外側ラベルを区別する（BF §1.2.4）。
方針：入力ラベル直和分解の逆の単射性を使う。
規約：挿入位置と異なる外側ラベルを扱う。
使われ方：残る外側二文字の隣接非一致を保つ。 -/
lemma remainingPosition_injective (m n : ℕ) (k : Fin (m + 1)) :
    Function.Injective (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) := by
  intro a b he
  exact Sum.inl.inj ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.injective he)

/-- 概要：挿入ラベルへの移動は部分語の隣接非一致を保つ（BF §1.2.4）。
方針：単射性で隣接する値の一致を元の部分語へ戻す。
規約：部分語は空でもよい。
使われ方：合成語の内側に由来する隣接位置を処理する。 -/
lemma isChain_map_inserted {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin n))
    (h : xs.IsChain (· ≠ ·)) :
    (xs.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)).IsChain (· ≠ ·) := by
  exact List.isChain_map_of_isChain _
    (fun a b hab he => hab (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k he)) h

/-- 概要：内側部分語の後に外側ラベルを置いても隣接重複は生じない（BF §1.2.4）。
方針：内側の末尾値と次の外側ラベルの非交差を使う。
規約：後続全体の隣接非一致を保持する。
使われ方：指定値の置換部分語とその直後の外側語の境界を処理する。 -/
lemma inserted_append_remaining_chain {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin n)) (a : {a : Fin (m + 1) // a ≠ k}) (tail : List (Fin (m + n)))
    (hx : xs.IsChain (· ≠ ·))
    (ht : (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a :: tail).IsChain (· ≠ ·)) :
    (xs.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a :: tail).IsChain (· ≠ ·) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_map_inserted k xs hx).append ht
  intro x hx y hy
  have hy' : _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a = y := by simpa using hy
  subst y
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_getLast? hx)
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k a b).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
