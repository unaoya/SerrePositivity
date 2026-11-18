module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseScheduleTransfer
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.InsertedOccurrences

/-!
模型。文献の定義との比較は後で
# 逆 Schedule の挿入位置の出現

概要：Berger–Fresse §1.4.4 の逆抽出で挿入点と直前出現を同定する。
方針：短縮行末の値と二つの不出現条件を、成功出力の連結表示へ適用する。
規約：元の出力と変更後の出力の非退化性は仮定しない。
使われ方：実際の逆削除の符号を短縮行の行番号へ戻す。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：元の削除位置は先行出力と短縮行の直後（BF §1.4.4）。
方針：元の行末の部分和と短縮行長を比較する。
規約：位置は零始まり。
使われ方：挿入点と短縮行末の座標を語の連結表示で評価する。 -/
lemma source_position (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    q.val = b.context.picked.flatten.length + b.left.length := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r b.early
  have hp := b.context.prefix_length
  have hl := b.left_length
  have hq := b.row_end
  have hh := b.long
  omega

/-- 概要：逆 Schedule の短縮行末は元の行末の直前（BF §1.4.4）。
方針：探索分割を実際の行リストへ戻し、共通の先行行の長さを比較する。
規約：短縮後も正の行長を持つ。
使われ方：直前出現の座標を新しい Schedule の行末へ移す。 -/
lemma shortened_end (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long) b.early + 1 = q.val := by
  have hsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = b.context.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val) ::
        (b.earlier ++ b.chosen :: b.later) := by
    rw [b.context.split, b.search.decomposition]
  have hchosen : b.chosen = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late, (r.val b.late).val) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_value_at_split (fun k => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w k, (r.val k).val))
      (b.context.before ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val) :: b.earlier) b.later b.chosen
      (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow, List.append_assoc, List.cons_append] using hsplit) b.late (by
        simp only [List.length_append, List.length_cons]
        have := b.late_index
        omega)
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_reverse_transfer_blocks w r b.early.castSucc b.late
    (ne_of_lt b.order) b.long b.context.before b.earlier b.later
    (by rw [← hchosen]; exact hsplit) b.context.before_length b.late_index.symm
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w _ b.context.before _ he b.early.castSucc
    b.context.before_length
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r b.context.before _ b.context.split b.early.castSucc
    b.context.before_length
  have hoff := hs.symm.trans ht
  have hend := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long) b.early
  rw [hoff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_donor] at hend
  have hold := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r b.early
  have hq := b.row_end
  have hl := b.long
  omega

/-- 概要：逆抽出の挿入点は挿入値の最終出現（BF §1.4.4）。
方針：後続語に挿入値がないことを実際の成功出力へ移す。
規約：出力が退化していても成立する。
使われ方：逆削除を最終出現側の削除集合へ送る。 -/
lemma point_not_caesura (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin b.new.length => b.new[j.val]) b.point := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.not_caesura_at_insert b.new
    ((b.context.picked.flatten ++ b.left) ++ b.middle) b.right b.a
    (by simpa only [List.append_assoc] using b.target_shape) b.absent_right b.point
  simp only [List.length_append]
  have := b.source_position
  have := b.point_value
  omega

/-- 概要：逆抽出の挿入値は短縮行末にも現れ、それが直前出現（BF §1.4.4）。
方針：短縮行を末尾で分け、中間語の不出現から最大の先行出現を計算する。
規約：直前出現の添字は元の削除位置から一つ戻ったもの。
使われ方：最終出現側の削除符号と順方向の受け取り行を同定する。 -/
lemma point_previousOccurrence (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    ∃ hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin b.new.length => b.new[j.val]) b.point).Nonempty,
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin b.new.length => b.new[j.val]) b.point).max' hp).val +
        1 = q.val := by
  obtain ⟨head, hhead⟩ := b.left_end
  have hleft : b.left.length = head.length + 1 := by
    simpa only [List.length_append, List.length_singleton] using congrArg List.length hhead
  have hsource := b.source_position
  have hpoint := b.point_value
  let p : Fin b.new.length := ⟨b.context.picked.flatten.length + head.length, by
    have := b.point.isLt
    omega⟩
  have hs : b.new = (b.context.picked.flatten ++ head) ++
      b.a :: (b.middle ++ b.a :: b.right) := by
    rw [b.target_shape, hhead]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.previousOccurrence_double_insert b.new
    (b.context.picked.flatten ++ head) b.middle b.right b.a hs b.absent_middle p b.point
    (by simp only [List.length_append]; rfl) (by
      simp only [List.length_append]
      omega)
  refine ⟨hp, ?_⟩
  rw [he]
  change b.context.picked.flatten.length + head.length + 1 = q.val
  omega

end ReverseTransferData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
