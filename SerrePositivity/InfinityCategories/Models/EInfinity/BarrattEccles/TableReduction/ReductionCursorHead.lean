module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorRemainder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorSlot

/-!
模型。文献の定義との比較は後で
# 指定位置まで進めた外側行の先頭の指定値

概要：Berger–Fresse §1.5.7 の垂直成分を始める元の外側進行状態を計算する。
方針：元の指定値の前半を除外し、利用可能行の残りを指定値と後半へ分ける。
規約：指定値自身は除外せず先頭に残す。
使われ方：元の成功から固定外側の垂直転送の先頭条件を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の指定出力位置まで進めた利用可能行は指定値を先頭に持つ（BF §1.5.7）。
方針：元の行の一出現の前半を除外し、drop で前半全体を消す。
規約：後半は指定値以外の部分型のリスト。
使われ方：垂直成分の転送で外側行の追加仮定を要求しない。 -/
lemma reductionRemoved_available_slot {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d)
    (v : Fin (m + 1 + d) → Fin (m + 1))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (m + 1 + d)) (k : Fin (m + 1)) (hk : v p = k) :
    ∃ post : List {a : Fin (m + 1) // a ≠ k},
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p)
        (List.ofFn (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)).symm) = k :: post.map Subtype.val := by
  let c := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h p
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v h p
  obtain ⟨pre, post, hs, hl⟩ := c.available_slot_split p j
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn_position w r v h p) k hk
  refine ⟨post, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (c.removed ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p))).take j.val)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)) = _
  rw [c.available_remainder j, hs]
  have he : j.val = (pre.map Subtype.val).length := by simpa only [List.length_map] using hl.symm
  rw [he, List.drop_append_length]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
