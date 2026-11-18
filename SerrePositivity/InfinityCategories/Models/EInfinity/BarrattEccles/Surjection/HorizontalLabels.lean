module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateUpdate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RemainingLettersValues

/-!
模型。文献の定義との比較は後で
# 内側の先頭文字を使う水平行のラベル写像

概要：Berger–Fresse §1.5.7 の水平成分で指定値を内側の現在の先頭文字へ移す。
方針：指定値は挿入ラベル、他の文字は既存の残りラベル写像で送る。
規約：内側の先頭文字を固定する。
使われ方：最終除外前の水平行の出力と除外更新を計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平成分の外側文字を合成ラベルへ移す写像（BF §1.5.7）。
方針：指定値だけを内側の現在の先頭文字へ置く。
規約：外側 arity m+1、内側 arity n。
使われ方：水平成分の元の選択語を実際の合成語へ移す。 -/
def horizontalLabel {m n : ℕ} (k : Fin (m + 1)) (b : Fin n) (a : Fin (m + 1)) :
    Fin (m + n) :=
  if h : a = k then insertedPosition m n k b else remainingPosition m n k ⟨a, h⟩

/-- 概要：指定値の水平ラベルは内側の先頭の挿入ラベル（BF §1.5.7）。
方針：指定値の分岐を評価する。
規約：任意の内側先頭文字。
使われ方：指定値を選択行末として通る水平抽出。 -/
@[simp] lemma horizontalLabel_slot {m n : ℕ} (k : Fin (m + 1)) (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b k = insertedPosition m n k b := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel, dite_eq_left rfl]

/-- 概要：他の外側文字の水平ラベルは残りラベル（BF §1.5.7）。
方針：部分型の非一致証明で指定値以外の分岐を選ぶ。
規約：指定値以外の部分型を使う。
使われ方：水平成分の通常の外側文字を移す。 -/
@[simp] lemma horizontalLabel_remaining {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (a : {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b a.val = remainingPosition m n k a := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel, dite_eq_right a.property]

/-- 概要：指定値のない追加除外を水平ラベルで移すと元の合成状態の更新（BF §1.5.7）。
方針：追加語を残り文字の部分型へ移し、既存の内外状態の更新公式を使う。
規約：追加する語には指定値がない。
使われ方：水平行の末尾以外の除外更新を合成状態へ移す。 -/
lemma horizontalLabel_state_update {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (xs : List (Fin (m + 1)))
    (hk : k ∉ xs) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++ xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ xs) inner := by
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k xs hk
  have hm : xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map (remainingPosition m n k) := by
    calc
      _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by rw [hv]
      _ = _ := by simp only [List.map_map, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_remaining]
  rw [hm]
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved_update k outer inner [] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs) x
  simpa only [List.map_nil, List.append_nil, hv] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
