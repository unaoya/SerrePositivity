module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionLabels

/-!
模型。文献の定義との比較は後で
# 合成表の内外の除外文字

概要：Berger–Fresse §1.5.7 の合成 table の除外状態を内外の文字から作る。
方針：外側の指定値を除いた文字と内側の文字を別々の単射で移す。
規約：外側の指定値自身はこの除外リストに寄与しない。
使われ方：利用可能な合成行のフィルターを元の二つのフィルターへ分解する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：語から指定値以外の文字を部分型として取り出す（BF §1.5.7）。
方針：指定値だけを filterMap で捨てる。
規約：文字の順序と重複を保持する。
使われ方：外側の除外文字を合成 arity へ移す。 -/
def remainingLetters {m : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1))) :
    List {a : Fin (m + 1) // a ≠ k} :=
  xs.filterMap (fun a => if h : a = k then none else some ⟨a, h⟩)

/-- 概要：部分型への抽出は指定値以外の所属を保存する（BF §1.5.7）。
方針：filterMap の所属を、指定値以外の文字の証人と同定する。
規約：部分型の文字は指定値と異なる。
使われ方：合成の除外所属を元の所属へ戻す。 -/
@[simp] lemma mem_remainingLetters {m : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (a : {a : Fin (m + 1) // a ≠ k}) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs ↔ a.val ∈ xs := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, he⟩
    split_ifs at he with h
    have hv : b = a.val := congrArg Subtype.val (Option.some.inj he)
    exact hv ▸ hb
  · intro ha
    exact ⟨a.val, ha, by simp only [dite_eq_right a.property]⟩

/-- 概要：内外の除外文字を合成 arity のリストへ集める（BF §1.5.7）。
方針：外側の残り文字と内側の挿入文字を連結する。
規約：リスト順序を選ぶが後の利用可能行は所属だけに依存する。
使われ方：合成 table の一行の除外状態。 -/
def compositionRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) : List (Fin (m + n)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k outer).map (remainingPosition m n k) ++
    inner.map (insertedPosition m n k)

/-- 概要：合成の外側除外所属は元の外側除外所属と同値（BF §1.5.7）。
方針：内外ラベルの非交差と外側ラベル写像の単射性を使う。
規約：指定値以外の外側文字について述べる。
使われ方：合成行の外側ブロックのフィルターを計算する。 -/
@[simp] lemma remaining_mem_compositionRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    remainingPosition m n k a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner ↔ a.val ∈ outer := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved, List.mem_append,
    List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_remainingLetters]
  have hn : remainingPosition m n k a ∉ inner.map (insertedPosition m n k) := by
    intro h
    obtain ⟨b, _, he⟩ := List.mem_map.mp h
    exact remainingPosition_ne_inserted m n k a b he.symm
  simp only [hn, or_false]

/-- 概要：合成の内側除外所属は元の内側除外所属と同値（BF §1.5.7）。
方針：内外ラベルの非交差と内側ラベル写像の単射性を使う。
規約：零 arity では入力がない。
使われ方：合成行の内側ブロックのフィルターを計算する。 -/
@[simp] lemma inserted_mem_compositionRemoved {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (b : Fin n) :
    insertedPosition m n k b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner ↔ b ∈ inner := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved, List.mem_append,
    List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k)]
  have hn : insertedPosition m n k b ∉
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k outer).map (remainingPosition m n k) := by
    intro h
    obtain ⟨a, _, he⟩ := List.mem_map.mp h
    exact remainingPosition_ne_inserted m n k a b he
  simp only [hn, false_or]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
