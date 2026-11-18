module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalWordSubstitution

/-!
模型。文献の定義との比較は後で
# 指定値の出現から始まる水平語の代入表示

概要：Berger–Fresse §1.5.7 の中間・最終水平語を、共有先頭文字と出現間の代入へ分解する。
方針：元の指定出現を先頭として分離し、内部の不出現を使う。
規約：閉区間の末尾を省く場合と最終尾部の全てを残す場合を区別する。
使われ方：全融合語の水平成分と compositeWord の後続代入を接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定出現から次の出現直前までの水平語を代入へ分解（BF §1.5.7）。
方針：閉区間の末尾を省き、先頭の指定値と不出現の内部を分ける。
規約：両端は異なる位置。
使われ方：全中間水平成分の実際の語の比較。 -/
lemma horizontal_interval_dropLast {m n l : ℕ} (v : Fin l → Fin (m + 1))
    (k : Fin (m + 1)) (b : Fin n) (p q : Fin l) (hpq : p < q) (hpk : v p = k)
    (parts : List (List (Fin n)))
    (hk : k ∉ ((List.ofFn v).drop (p.val + 1)).take (q.val - (p.val + 1))) :
    ((((List.ofFn v).drop p.val).take (q.val - p.val + 1)).map
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b)).dropLast =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (((List.ofFn v).drop (p.val + 1)).take (q.val - (p.val + 1))) parts := by
  have hp : p.val < (List.ofFn v).length := by simpa only [List.length_ofFn] using p.isLt
  have hb : q.val - p.val + 1 ≤ ((List.ofFn v).drop p.val).length := by
    simp only [List.length_drop, List.length_ofFn]
    have := q.isLt
    change p.val < q.val at hpq
    omega
  have he : q.val - p.val - 1 = q.val - (p.val + 1) := by omega
  rw [← List.map_dropLast, List.dropLast_take hb, Nat.add_sub_cancel,
    ← List.getElem_cons_drop hp, List.take_cons (by change p.val < q.val at hpq; omega),
    List.map_cons, List.getElem_ofFn, hpk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_slot, he,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_horizontal_no_slot k b _ _ hk]

/-- 概要：指定出現からの最終尾部の水平語を代入へ分解（BF §1.5.7）。
方針：指定値の先頭を分け、それ以降に指定値がないことを使う。
規約：指定出現が最終位置なら後続は空語。
使われ方：最終水平成分の実際の語の比較。 -/
lemma horizontal_suffix_from_slot {m n l : ℕ} (v : Fin l → Fin (m + 1))
    (k : Fin (m + 1)) (b : Fin n) (p : Fin l) (hpk : v p = k)
    (parts : List (List (Fin n))) (hk : k ∉ (List.ofFn v).drop (p.val + 1)) :
    ((List.ofFn v).drop p.val).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop (p.val + 1)) parts := by
  have hp : p.val < (List.ofFn v).length := by simpa only [List.length_ofFn] using p.isLt
  rw [← List.getElem_cons_drop hp, List.map_cons, List.getElem_ofFn, hpk,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_slot, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_horizontal_no_slot k b _ _ hk]

namespace TableCompositionData

/-- 概要：中間水平語は共有先頭文字と連続出現間の代入の連結（BF §1.5.7）。
方針：連続する出現境界を元の位置へ戻し、その間の不出現を使う。
規約：前後の出現番号は隣接する。
使われ方：垂直成分末尾と次の水平語先頭を一つに戻す。 -/
lemma middleHorizontal_dropLast {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i j : Fin c.count) (hij : j.val = i.val + 1) :
    (c.horizontalWord j.val).dropLast =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot (c.innerWord.val (c.innerPosition j.val)) ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
          (((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)).take
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val -
              ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)))
          ((c.cuts.segments c.innerWord.val).drop j.val) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot j.val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val := by
    rw [hij]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_at c.outerWord.val c.slot i
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_at c.outerWord.val c.slot j
  have hpq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono c.outerWord.val c.slot
    (show i < j by change i.val < j.val; omega)
  have hk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice c.outerWord.val c.slot
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val (fun p hp hq =>
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_between c.outerWord.val c.slot i j hij p
        (by change _ < p.val; omega) hq)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord, hs, ht]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_interval_dropLast c.outerWord.val c.slot _ _ _ hpq
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value c.outerWord.val c.slot i) _ hk

/-- 概要：最終水平語は共有先頭文字と最終出現後の代入の連結（BF §1.5.7）。
方針：最後の閉区間を元の最終尾部へ戻し、最後の出現以降の不出現を使う。
規約：最後の指定値が元の語の最終位置でも成立する。
使われ方：全融合語と代入語の後ろからの帰納の末尾。 -/
lemma finalHorizontal_word {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) (hi : i.val + 1 = c.count) :
    c.horizontalWord c.count =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot (c.innerWord.val (c.innerPosition c.count)) ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
          ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1))
          ((c.cuts.segments c.innerWord.val).drop c.count) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot c.count =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val := by
    rw [← hi]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_at c.outerWord.val c.slot i
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice c.outerWord.val c.slot
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1) (m + 1 + d)
    (fun p hp _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_after_last c.outerWord.val c.slot i hi p
      (by change _ < p.val; omega))
  have hl : ((List.ofFn c.outerWord.val).drop
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)).length =
      m + 1 + d - ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1) := by
    simp only [List.length_drop, List.length_ofFn]
  rw [← hl, List.take_length] at hn
  have he : m + 1 + d - 1 - (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1 =
      ((List.ofFn c.outerWord.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val).length := by
    simp only [List.length_drop, List.length_ofFn]
    have := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).isLt
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord, hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_last, he, List.take_length]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_suffix_from_slot c.outerWord.val c.slot _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value c.outerWord.val c.slot i) _ hn

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
