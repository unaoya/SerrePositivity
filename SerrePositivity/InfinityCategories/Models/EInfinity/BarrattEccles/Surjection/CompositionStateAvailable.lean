module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateRemoved
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionAvailable

/-!
模型。文献の定義との比較は後で
# 合成状態の全段階での利用可能なブロック

概要：Berger–Fresse §1.5.7 の指定値の最終除外後も含めた行フィルターを計算する。
方針：外側の所属条件は不変、内側は指定値の除外後に全て消えることを使う。
規約：元の内側除外リストに重複があってもよい。
使われ方：実際の合成行の表示と全段階での抽出更新。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全段階の状態で外側ブロックは元の外側除外だけに依存（BF §1.5.7）。
方針：内外の非交差による除外所属の同値を filter-map へ適用する。
規約：外側指定値の除外済みかどうかに依存しない。
使われ方：合成行の前半と後半の計算。 -/
lemma available_state_remaining_block {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n))
    (xs : List {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) (xs.map (remainingPosition m n k)) =
      (xs.filter (fun a => a.val ∉ outer)).map (remainingPosition m n k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_map, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionStateRemoved]

/-- 概要：外側指定値の除外後は内側ブロックが空（BF §1.5.7）。
方針：全ての挿入ラベルが合成の除外状態に属することを使う。
規約：内側 arity 零も含む。
使われ方：最後の指定値の後の外側成分を抽出する。 -/
lemma available_state_inserted_of_mem {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner xs : List (Fin n)) (hk : k ∈ outer) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) (xs.map (insertedPosition m n k)) = [] := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_map, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionStateRemoved,
    hk, or_true, not_true_eq_false, decide_false, List.filter_false, List.map_nil]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
