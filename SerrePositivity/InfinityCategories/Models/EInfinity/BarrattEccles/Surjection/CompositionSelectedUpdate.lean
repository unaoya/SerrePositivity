module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateFinalize

/-!
模型。文献の定義との比較は後で
# 選択行の末尾を残す合成除外更新

概要：Berger–Fresse §1.5.7 の三種類の選択長さで実際の除外更新を計算する。
方針：take(選択長さ−1) を内外の先頭部分へ直し、除外状態の更新公式を使う。
規約：選択長さは正であり、最後に選んだ文字は除外へ加えない。
使われ方：元の reduceRows の再帰で合成抽出を一行進める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定値より前で止まる行の末尾以外の除外更新（BF §1.5.7）。
方針：前半内の先頭部分の式を内外状態の更新へ適用する。
規約：選択長さは前半の長さ以内。
使われ方：指定値の前の水平行の実際の状態更新。 -/
lemma compositionSelectedUpdate_before {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (r : ℕ) (hr : r ≤ pre.length)
    (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys]).take (r - 1) ↔
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ (pre.take (r - 1)).map Subtype.val) inner := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_before k pre post ys (r - 1) (by omega)]
  simpa only [List.map_nil, List.append_nil] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved_update k outer inner [] (pre.take (r - 1)) x

/-- 概要：内側で止まる行の末尾以外の除外更新（BF §1.5.7）。
方針：前半の全外側文字と内側の末尾以外を個別の除外状態へ加える。
規約：内側から正の長さ r を選ぶ。
使われ方：垂直行の実際の除外更新。 -/
lemma compositionSelectedUpdate_inside {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (r : ℕ)
    (hr : 0 < r) (hb : r ≤ ys.length) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys]).take
        (pre.length + r - 1) ↔
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ pre.map Subtype.val) (inner ++ ys.take (r - 1)) := by
  have he : pre.length + r - 1 = pre.length + (r - 1) := by omega
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_inside k pre post ys (r - 1) (by omega)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved_update k outer inner (ys.take (r - 1)) pre x

/-- 概要：内側全体を通過する行の末尾以外の除外更新（BF §1.5.7）。
方針：前半と後半の先頭部分を外側へ加え、内側全被覆から指定値を最終除外する。
規約：後半から正の長さ r を選ぶ。
使われ方：最後の指定値を通過した水平行の実際の状態更新。 -/
lemma compositionSelectedUpdate_after {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (r : ℕ) (hr : 0 < r)
    (hcover : ∀ b : Fin n, b ∈ inner ∨ b ∈ ys) (x : Fin (m + n)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys]).take
        (pre.length + ys.length + r - 1) ↔
    x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (outer ++ k :: (pre ++ post.take (r - 1)).map Subtype.val) inner := by
  have he : pre.length + ys.length + r - 1 = pre.length + ys.length + (r - 1) := by omega
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_after]
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved_finalize k outer inner ys
    (pre ++ post.take (r - 1)) hcover x
  simp only [List.map_append, List.mem_append] at hf ⊢
  tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
