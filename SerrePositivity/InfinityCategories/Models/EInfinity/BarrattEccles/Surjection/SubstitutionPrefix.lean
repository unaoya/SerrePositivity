module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionOneSlot

/-!
模型。文献の定義との比較は後で
# 一出現代入の三ブロック内の先頭部分

概要：Berger–Fresse §1.5.7 の合成行から選ぶ先頭部分を内外の文字で計算する。
方針：指定値の前・内側・指定値の後で take の連結公式を使う。
規約：境界上の長さ零の部分も許す。
使われ方：選択行と、その末尾以外を除外する更新の両方へ適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定値より前で止まる先頭部分は外側の先頭部分（BF §1.5.7）。
方針：最初のブロックの長さ以内の take を計算する。
規約：内側文字列が空でも成立する。
使われ方：指定値より前の水平成分の抽出。 -/
lemma substitute_one_slot_take_before {m n : ℕ} (k : Fin (m + 1))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (inner : List (Fin n))
    (r : ℕ) (hr : r ≤ pre.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [inner]).take r =
      (pre.take r).map (remainingPosition m n k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot, List.take_append_of_le_length (by simpa only [List.length_map] using hr),
    ← List.map_take]

/-- 概要：内側ブロック内で止まる先頭部分は外側前半と内側先頭部分（BF §1.5.7）。
方針：最初のブロックを全て取り、内側ブロックの長さ以内の take を計算する。
規約：内側の先頭長さ零も含む。
使われ方：垂直成分の選択語と除外更新の計算。 -/
lemma substitute_one_slot_take_inside {m n : ℕ} (k : Fin (m + 1))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (inner : List (Fin n))
    (r : ℕ) (hr : r ≤ inner.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [inner]).take
        (pre.length + r) =
      pre.map (remainingPosition m n k) ++ (inner.take r).map (insertedPosition m n k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]
  calc
    _ = pre.map (remainingPosition m n k) ++
        ((inner.map (insertedPosition m n k) ++
          post.map (remainingPosition m n k)).take r) := by
      simpa only [List.length_map] using List.take_length_add_append
        (l₁ := pre.map (remainingPosition m n k))
        (l₂ := inner.map (insertedPosition m n k) ++ post.map (remainingPosition m n k)) r
    _ = _ := by
      rw [List.take_append_of_le_length (by simpa only [List.length_map] using hr),
        ← List.map_take]

/-- 概要：後半で止まる先頭部分は前二ブロックと外側後半の先頭部分（BF §1.5.7）。
方針：前二ブロックを連結し、その全長の後の take を計算する。
規約：要求長さが後半より大きいときも通常の take として成立する。
使われ方：指定値を最後に通過した外側成分の選択と除外更新。 -/
lemma substitute_one_slot_take_after {m n : ℕ} (k : Fin (m + 1))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (inner : List (Fin n)) (r : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [inner]).take
        (pre.length + inner.length + r) =
      pre.map (remainingPosition m n k) ++ (inner.map (insertedPosition m n k) ++
        (post.take r).map (remainingPosition m n k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot, ← List.append_assoc]
  calc
    _ = (pre.map (remainingPosition m n k) ++ inner.map (insertedPosition m n k)) ++
        (post.map (remainingPosition m n k)).take r := by
      simpa only [List.length_append, List.length_map] using List.take_length_add_append
        (l₁ := pre.map (remainingPosition m n k) ++ inner.map (insertedPosition m n k))
        (l₂ := post.map (remainingPosition m n k)) r
    _ = _ := by rw [← List.map_take, List.append_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
