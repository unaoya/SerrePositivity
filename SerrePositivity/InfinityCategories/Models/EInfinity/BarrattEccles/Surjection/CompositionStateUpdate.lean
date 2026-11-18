module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateRemoved
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExclusionEquivalence

/-!
模型。文献の定義との比較は後で
# 合成表の内外の除外状態の更新

概要：Berger–Fresse §1.5.7 の選択後の除外状態を元の二表の更新と照合する。
方針：内外ラベルの直和分解で全ての所属を二種類へ分ける。
規約：除外リストの順序は固定せず、所属の同値を証明する。
使われ方：抽出の先頭部分を選択した後の合成状態の不変条件。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：外側ラベルは内側文字列の像に含まれない（BF §1.5.7）。
方針：内外ラベルの非交差を各文字へ適用する。
規約：文字列の重複は許す。
使われ方：除外リストの更新を所属ごとに計算する。 -/
@[simp] lemma remaining_not_mem_inserted_map {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (xs : List (Fin n)) :
    remainingPosition m n k a ∉ xs.map (insertedPosition m n k) := by
  intro h
  obtain ⟨b, _, he⟩ := List.mem_map.mp h
  exact remainingPosition_ne_inserted m n k a b he.symm

/-- 概要：内側ラベルは外側文字列の像に含まれない（BF §1.5.7）。
方針：内外ラベルの非交差を各文字へ適用する。
規約：外側文字は指定値以外の部分型。
使われ方：除外リストの更新を所属ごとに計算する。 -/
@[simp] lemma inserted_not_mem_remaining_map {m n : ℕ} (k : Fin (m + 1))
    (b : Fin n) (xs : List {a : Fin (m + 1) // a ≠ k}) :
    insertedPosition m n k b ∉ xs.map (remainingPosition m n k) := by
  intro h
  obtain ⟨a, _, he⟩ := List.mem_map.mp h
  exact remainingPosition_ne_inserted m n k a b he

/-- 概要：指定値は残り外側文字の値リストに含まれない（BF §1.5.7）。
方針：部分型の各文字の非一致証明を使う。
規約：文字列の順序は任意。
使われ方：指定値以外を除外しても指定値の除外状態は変わらない。 -/
@[simp] lemma slot_not_mem_remaining_values {m : ℕ} (k : Fin (m + 1))
    (xs : List {a : Fin (m + 1) // a ≠ k}) : k ∉ xs.map Subtype.val := by
  intro h
  obtain ⟨a, _, he⟩ := List.mem_map.mp h
  exact a.property he

/-- 概要：内外の追加除外は元の二状態の個別更新と同じ所属を与える（BF §1.5.7）。
方針：任意の合成ラベルを内側か残り外側かへ直和分解して比較する。
規約：追加する外側文字は指定値以外。リスト順序の一致は要求しない。
使われ方：外側指定値の最終除外を跨がない抽出更新の不変条件。 -/
lemma compositionStateRemoved_update {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner more : List (Fin n))
    (extra : List {a : Fin (m + 1) // a ≠ k}) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (extra.map (remainingPosition m n k) ++ more.map (insertedPosition m n k)) ↔
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ extra.map Subtype.val) (inner ++ more) := by
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective x
  cases a with
  | inl a =>
    change remainingPosition m n k a ∈ _ ↔ remainingPosition m n k a ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionStateRemoved,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_not_mem_inserted_map, or_false,
      List.mem_map_of_injective Subtype.val_injective]
  | inr b =>
    change insertedPosition m n k b ∈ _ ↔ insertedPosition m n k b ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionStateRemoved,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_not_mem_remaining_map, false_or,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.slot_not_mem_remaining_values, or_false]
    tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
