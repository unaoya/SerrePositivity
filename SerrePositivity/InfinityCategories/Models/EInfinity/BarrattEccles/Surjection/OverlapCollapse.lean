module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapCoverage

/-!
模型。文献の定義との比較は後で
# 重なる全分割成分の連結を縮約して元の語へ戻す

概要：Berger–Fresse §1.5.9 の内側語の復元で分割の共有端点の重複を取り除く。
方針：分割の後ろから各共有端点を一つずつ消し、元の語の尾部を復元する。
規約：元の語の非退化性は要求せず、縮約後の語を比較する。
使われ方：実際の合成語から元の非退化な内側語を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

/-- 概要：残る全分割成分の連結は縮約後に元の語の同じ尾部になる（BF §1.5.9）。
方針：隣接成分の共有開始位置と最後の成分の全長条件を使う。
規約：正の元の語長、値の型は任意。
使われ方：第零成分で全内側語を復元する。 -/
lemma collapse_segments_suffix {t l : ℕ} {α : Type*} [DecidableEq α]
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (v : Fin l → α) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (((r.segments v).drop i.val).flatten) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ((List.ofFn v).drop (r.start i)) := by
  have hp : i.val < (r.segments v).length := by simpa only [r.segments_length] using i.isLt
  have hx : (r.segments v).drop i.val =
      r.segment v i :: (r.segments v).drop (i.val + 1) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.getElem_ofFn] using (List.getElem_cons_drop hp).symm
  rw [hx, List.flatten_cons]
  by_cases hn : i.val + 1 < t
  · let j : Fin t := ⟨i.val + 1, hn⟩
    have ih := r.collapse_segments_suffix hl v j
    have hd : (List.ofFn v).drop (r.start j) =
        ((List.ofFn v).drop (r.start i)).drop ((r.val i).val - 1) := by
      rw [List.drop_drop, r.start_next i j rfl]
    have hb : (r.val i).val ≤ ((List.ofFn v).drop (r.start i)).length := by
      have hs := r.start_add_length_le i
      simp only [List.length_drop, List.length_ofFn]
      omega
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (r.segment v i ++ (List.ofFn v).drop (r.start j)) :=
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr _ _ _ ih
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (((List.ofFn v).drop (r.start i)).take (r.val i).val ++
          ((List.ofFn v).drop (r.start i)).drop ((r.val i).val - 1)) := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment, hd]
      _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_overlap_take _ _ (r.positive hl i) hb
  · have he : i.val + 1 = t := by have := i.isLt; omega
    have ht : (r.segments v).drop (i.val + 1) = [] := by
      rw [he]
      apply List.drop_eq_nil_of_le
      rw [r.segments_length]
    rw [ht, List.flatten_nil, List.append_nil]
    have hlen : (r.val i).val = ((List.ofFn v).drop (r.start i)).length := by
      have hs := r.last_end hl i he
      simp only [List.length_drop, List.length_ofFn]
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment, hlen, List.take_length]
termination_by t - i.val
decreasing_by omega

/-- 概要：全分割成分の連結を縮約すると元の語の縮約になる（BF §1.5.9）。
方針：第零成分の開始位置が零であることを後続復元へ渡す。
規約：分割数と元の語長は正。
使われ方：元の非退化な内側語を合成語から復元する。 -/
lemma collapse_segments {t l : ℕ} {α : Type*} [DecidableEq α]
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (ht : 0 < t) (v : Fin l → α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ((r.segments v).flatten) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn v) := by
  simpa only [Fin.val_zero, List.drop_zero, r.start_zero ht] using
    r.collapse_segments_suffix hl v ⟨0, ht⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
