module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionRemoved
public import Mathlib.Data.List.FinRange

/-!
模型。文献の定義との比較は後で
# 外側の指定値の最終除外を含む合成表の状態

概要：Berger–Fresse §1.5.7 の合成 table の除外状態を指定値の最終出現の後へ延長する。
方針：外側で指定値が除外された後は、全ての内側ラベルも除外する。
規約：それ以前は元の内側除外リストだけを使う。
使われ方：水平・垂直の抽出更新を一つの状態表示で記述する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定値の最終除外を含む内外の合成除外状態（BF §1.5.7）。
方針：指定値が外側で除外済みなら内側の全ラベルを除外リストへ加える。
規約：内側 arity 零では追加リストは空。
使われ方：合成 table の全進行段階の状態不変条件。 -/
def compositionStateRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) : List (Fin (m + n)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer (inner ++ if k ∈ outer then List.finRange n else [])

/-- 概要：指定値が未除外なら既存の合成除外リストと一致（BF §1.5.7）。
方針：全内側ラベルの追加がない分岐を計算する。
規約：リスト自身の等式。
使われ方：既存の未除外段階の利用可能行の式を再利用する。 -/
lemma compositionStateRemoved_of_not_mem {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (hk : k ∉ outer) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved, ite_eq_right hk, List.append_nil]

/-- 概要：合成状態の外側除外所属は元の外側所属（BF §1.5.7）。
方針：既存の内外ラベルの非交差を使う。
規約：指定値以外の文字について述べる。
使われ方：外側の選択後の状態更新を照合する。 -/
@[simp] lemma remaining_mem_compositionStateRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    remainingPosition m n k a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ↔ a.val ∈ outer := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionRemoved k outer _ a

/-- 概要：内側文字は元の内側除外または指定値の最終除外で消える（BF §1.5.7）。
方針：全内側ラベルの所属を計算する。
規約：内側の各文字についての必要十分条件。
使われ方：内側成分の抽出と外側指定値の最終除外を同じ式へまとめる。 -/
@[simp] lemma inserted_mem_compositionStateRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (b : Fin n) :
    insertedPosition m n k b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ↔
      b ∈ inner ∨ k ∈ outer := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionRemoved, List.mem_append]
  by_cases hk : k ∈ outer <;> simp only [hk, ite_true, ite_false, List.mem_finRange,
    List.not_mem_nil, or_true, or_false]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
