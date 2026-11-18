module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateUpdate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows
public import Mathlib.Data.List.OfFn

/-!
模型。文献の定義との比較は後で
# 指定値を最後に通過する除外状態の更新

概要：Berger–Fresse §1.5.7 の外側指定値を最終除外する段階を照合する。
方針：元の内側除外と全利用可能内側行が全ラベルを覆うことを使う。
規約：内側 arity 零でも被覆条件は空として成立する。
使われ方：内側ブロックの全通過後に外側の水平抽出を続ける。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の除外と利用可能な置換行は内側全ラベルを覆う（BF §1.5.7）。
方針：未除外の文字は逆置換行の一意な位置で利用可能になる。
規約：指定した置換は任意。
使われ方：全内側ブロック通過時の最終除外条件。 -/
lemma mem_removed_or_available_permutation {n : ℕ} (τ : Equiv.Perm (Fin n))
    (inner : List (Fin n)) (b : Fin n) :
    b ∈ inner ∨ b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) := by
  by_cases hb : b ∈ inner
  · exact Or.inl hb
  · right
    apply List.mem_filter.mpr
    exact ⟨List.mem_ofFn.mpr ⟨τ b, τ.symm_apply_apply b⟩, decide_eq_true hb⟩

/-- 概要：全内側文字の通過は外側指定値の最終除外と同じ合成状態（BF §1.5.7）。
方針：外側は追加文字の所属、内側は全ラベルの被覆で比較する。
規約：先頭部分の内外文字を加える順序は所属に影響しない。
使われ方：内側ブロック全体を除外した後の合成抽出の状態不変条件。 -/
lemma compositionStateRemoved_finalize {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner more : List (Fin n))
    (extra : List {a : Fin (m + 1) // a ≠ k})
    (hcover : ∀ b : Fin n, b ∈ inner ∨ b ∈ more) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (extra.map (remainingPosition m n k) ++ more.map (insertedPosition m n k)) ↔
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ k :: extra.map Subtype.val) inner := by
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective x
  cases a with
  | inl a =>
    change remainingPosition m n k a ∈ _ ↔ remainingPosition m n k a ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionStateRemoved,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_not_mem_inserted_map, or_false, List.mem_cons,
      List.mem_map_of_injective Subtype.val_injective, a.property, false_or]
  | inr b =>
    change insertedPosition m n k b ∈ _ ↔ insertedPosition m n k b ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionStateRemoved,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_not_mem_remaining_map, false_or,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k), List.mem_cons,
      true_or, or_true]
    apply iff_true_intro
    rcases hcover b with hb | hb
    · exact Or.inl (Or.inl hb)
    · exact Or.inr hb

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
