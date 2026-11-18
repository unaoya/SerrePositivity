module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalIntervalWords

/-!
模型。文献の定義との比較は後で
# 垂直成分語の末尾と次の水平先頭の一致

概要：Berger–Fresse §1.5.7 の垂直語の末尾が次の水平語の共有先頭文字であることを示す。
方針：分割成分の最後の添字を元の終了位置へ戻す。
規約：正の内側語長。一文字の成分も含む。
使われ方：dropLast で省いた垂直末尾を次の水平先頭で一度だけ復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：正の分割成分の最後の文字は元の終了位置の文字（BF §1.5.7）。
方針：成分長と drop・take の最終添字を評価する。
規約：値の型は任意。
使われ方：垂直語と次の水平語の共有文字を照合する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_last {t l : ℕ} {α : Type*} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    (hl : 0 < l) (v : Fin l → α) (i : Fin t) :
    (r.segment v i).getLast? = some (v (r.endPosition hl i)) := by
  have hp := r.positive hl i
  have hb := r.start_add_length_le i
  have he : r.start i + ((r.val i).val - 1) < l := by omega
  rw [List.getLast?_eq_getElem?, r.segment_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, List.getElem?_ofFn,
    dite_eq_left he]
  congr 2
  apply Fin.ext
  change r.start i + ((r.val i).val - 1) = r.start i + (r.val i).val - 1
  omega

namespace TableCompositionData

/-- 概要：垂直語は末尾を省いた語と次の水平先頭文字の連結（BF §1.5.7）。
方針：実際の分割終了位置と次の内側境界の一致を使う。
規約：最後の垂直から最終水平への接続も同じ式。
使われ方：全融合語の隣接成分を実際の代入語へ接続する。 -/
lemma verticalWord_append_endpoint {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) : c.verticalWord i = (c.verticalWord i).dropLast ++
      [_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot
        (c.innerWord.val (c.innerPosition (i.val + 1)))] := by
  have hl : (c.verticalWord i).getLast? = some (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot
      (c.innerWord.val (c.innerPosition (i.val + 1)))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalWord, List.getLast?_map, c.cuts.segment_last c.inner_positive,
      Option.map_some, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.innerPosition, c.cuts.boundaryPosition_next]
  obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp hl
  rw [he, List.dropLast_concat]

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
