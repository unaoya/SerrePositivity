module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSelectedUpdate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows

/-!
模型。文献の定義との比較は後で
# 合成表の一行の成功抽出

概要：Berger–Fresse §1.5.7 の三種類の行を元の reduceRows の成功分岐へ接続する。
方針：実際の利用可能行の表示と末尾以外の状態更新から後続抽出を輸送する。
規約：内外ラベルの順序を保ち、除外状態の順序だけは所属の同値で比較する。
使われ方：shuffle 経路に沿って成功した抽出を一行ずつ組み立てる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値より前で止まる行の成功抽出（BF §1.5.7）。
方針：前半内の選択語と除外更新を既存の一行の成功規則に渡す。
規約：利用可能行の代入表示は実際の置換行の定理から得る。
使われ方：指定値の前の水平成分を元の抽出へ追加する。 -/
lemma compositionExtractionStep_before {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (row : List (Fin (m + n)))
    (r : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys])
    (hr : 0 < r) (hb : r ≤ pre.length)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ (pre.take (r - 1)).map Subtype.val) inner) =
        some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some ((pre.take r).map (remainingPosition m n k) ++ tail) := by
  have hlen : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).length := by
    rw [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]
    simp only [List.length_append, List.length_map]
    omega
  have hup : ∀ x, x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take (r - 1) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ (pre.take (r - 1)).map Subtype.val) inner := by
    intro x
    rw [hrow]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSelectedUpdate_before k outer inner ys pre post r hb x
  have ht' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ hup).trans ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row r rest _ tail hr hlen ht'
  simpa only [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_before k pre post ys r hb] using hs

/-- 概要：内側で止まる行の成功抽出（BF §1.5.7）。
方針：外側前半と内側の先頭を選び、末尾の内側文字を残す状態へ後続を輸送する。
規約：内側から正の長さ r を選ぶ。
使われ方：垂直成分を元の抽出へ追加する。 -/
lemma compositionExtractionStep_inside {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (row : List (Fin (m + n)))
    (r : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys])
    (hr : 0 < r) (hb : r ≤ ys.length)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (outer ++ pre.map Subtype.val) (inner ++ ys.take (r - 1))) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, pre.length + r) :: rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some ((pre.map (remainingPosition m n k) ++
        (ys.take r).map (insertedPosition m n k)) ++ tail) := by
  have hlen : pre.length + r ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).length := by
    rw [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]
    simp only [List.length_append, List.length_map]
    omega
  have hup : ∀ x, x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take (pre.length + r - 1) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ pre.map Subtype.val)
        (inner ++ ys.take (r - 1)) := by
    intro x
    rw [hrow]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSelectedUpdate_inside k outer inner ys pre post r hr hb x
  have ht' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ hup).trans ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (pre.length + r) rest _ tail (by omega) hlen ht'
  simpa only [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_inside k pre post ys r hb] using hs

/-- 概要：内側全体を通過した行の成功抽出（BF §1.5.7）。
方針：後半の末尾を残し、内側全被覆から指定値の最終除外状態へ後続を輸送する。
規約：後半から正の長さ r を選ぶ。
使われ方：最後の指定値を通過した水平成分を元の抽出へ追加する。 -/
lemma compositionExtractionStep_after {m n : ℕ} (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner ys : List (Fin n))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (row : List (Fin (m + n)))
    (r : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [ys])
    (hr : 0 < r) (hb : r ≤ post.length) (hcover : ∀ b : Fin n, b ∈ inner ∨ b ∈ ys)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (outer ++ k :: (pre ++ post.take (r - 1)).map Subtype.val) inner) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, pre.length + ys.length + r) :: rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some ((pre.map (remainingPosition m n k) ++ (ys.map (insertedPosition m n k) ++
        (post.take r).map (remainingPosition m n k))) ++ tail) := by
  have hlen : pre.length + ys.length + r ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).length := by
    rw [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]
    simp only [List.length_append, List.length_map]
    omega
  have hup : ∀ x, x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take
        (pre.length + ys.length + r - 1) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
        (outer ++ k :: (pre ++ post.take (r - 1)).map Subtype.val) inner := by
    intro x
    rw [hrow]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSelectedUpdate_after k outer inner ys pre post r hr hcover x
  have ht' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ hup).trans ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (pre.length + ys.length + r) rest _ tail
    (by omega) hlen ht'
  simpa only [hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot_take_after] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
