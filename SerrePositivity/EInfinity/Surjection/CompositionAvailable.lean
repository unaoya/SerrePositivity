module

public import SerrePositivity.EInfinity.Surjection.CompositionRemoved
public import SerrePositivity.EInfinity.TableReduction.Rows

/-!
# 合成の除外状態での各ブロックの利用可能行

概要：Berger–Fresse §1.5.7 の合成行のフィルターを内外のフィルターへ分ける。
方針：除外所属の同値を filter と map の交換に適用する。
規約：指定値以外の外側ラベルは部分型で保持する。
使われ方：実際の置換行への代入と先行行の除外処理の両立。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：外側ブロックの利用可能文字は元の外側除外で決まる（BF §1.5.7）。
方針：filter-map の交換と外側除外所属の同値を使う。
規約：文字の順序と重複を保持する。
使われ方：合成行の前半と後半を計算する。 -/
lemma available_remaining_block {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n))
    (xs : List {a : Fin (m + 1) // a ≠ k}) :
    available (compositionRemoved k outer inner) (xs.map (remainingPosition m n k)) =
      (xs.filter (fun a => a.val ∉ outer)).map (remainingPosition m n k) := by
  simp only [available, List.filter_map, Function.comp_def, remaining_mem_compositionRemoved]

/-- 概要：内側ブロックの利用可能文字は元の内側除外で決まる（BF §1.5.7）。
方針：filter-map の交換と内側除外所属の同値を使う。
規約：零 arity の空ブロックも含む。
使われ方：合成行の内側ブロックを計算する。 -/
lemma available_inserted_block {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner xs : List (Fin n)) :
    available (compositionRemoved k outer inner) (xs.map (insertedPosition m n k)) =
      (available inner xs).map (insertedPosition m n k) := by
  simp only [available, List.filter_map, Function.comp_def, inserted_mem_compositionRemoved]

/-- 概要：元の外側ブロックのフィルターは部分型を保って計算できる（BF §1.5.7）。
方針：filter-map の交換を部分型の値写像へ適用する。
規約：指定値以外の文字だけを扱う。
使われ方：元の外側行を再び一出現の代入の形へ分ける。 -/
lemma available_remaining_values {m : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (xs : List {a : Fin (m + 1) // a ≠ k}) :
    available outer (xs.map Subtype.val) =
      (xs.filter (fun a => a.val ∉ outer)).map Subtype.val := by
  simp only [available, List.filter_map, Function.comp_def]

end SerrePositivity.EInfinity.Surjection
