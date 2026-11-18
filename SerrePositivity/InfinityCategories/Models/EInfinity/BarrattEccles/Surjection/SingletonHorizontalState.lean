module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalLabelImages
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateFinalize

/-!
模型。文献の定義との比較は後で
# 内側一文字の最終水平成分での合成除外更新

概要：Berger–Fresse §1.5.7 の最後の指定値の除外を含む任意の水平更新を計算する。
方針：固定文字以外の内側文字が既に除外されていることを使う。
規約：外側の追加除外に指定値が含まれてもよい。
使われ方：最後の外側水平成分を一行ずつ転送する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：可用行が一文字なら他の内側文字は全て除外済み（BF §1.5.7）。
方針：元の除外と利用可能な置換行の全被覆を使う。
規約：内側文字の非退化性は元の置換行だけから得る。
使われ方：指定値の最終除外で残りの内側文字の更新を照合する。 -/
lemma singleton_inner_cover {n : ℕ} (τ : Equiv.Perm (Fin n)) (inner : List (Fin n))
    (b : Fin n) (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = [b]) (c : Fin n) :
    c ∈ inner ∨ c = b := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_removed_or_available_permutation τ inner c with hc | hc
  · exact Or.inl hc
  · rw [hinner] at hc
    exact Or.inr (List.mem_singleton.mp hc)

/-- 概要：内側が固定一文字以外を除外済みなら任意の水平除外更新が正しい（BF §1.5.7）。
方針：内外ラベルの所属を分け、他の内側文字は既除外であることを使う。
規約：追加語に指定値がある場合も含める。
使われ方：最終水平成分の途中で指定値と最後の内側文字を同時に除外する。 -/
lemma horizontalLabel_singleton_state_update {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (xs : List (Fin (m + 1)))
    (hcover : ∀ c : Fin n, c ∈ inner ∨ c = b) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++ xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ xs) inner := by
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective x
  cases a with
  | inl a =>
    change remainingPosition m n k a ∈ _ ↔ remainingPosition m n k a ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionStateRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_horizontal_map]
  | inr c =>
    change insertedPosition m n k c ∈ _ ↔ insertedPosition m n k c ∈ _
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionStateRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_horizontal_map]
    rcases hcover c with hc | hc
    · simp only [hc, true_or]
    · subst c
      simp only [true_and]
      tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
