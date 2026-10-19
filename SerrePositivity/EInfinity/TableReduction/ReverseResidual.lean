module

public import SerrePositivity.EInfinity.TableReduction.ReverseRowPrefix
public import SerrePositivity.EInfinity.TableReduction.RowInterior
public import SerrePositivity.EInfinity.TableReduction.UniqueInsertion

/-!
# 逆構成の挿入点は残余削除集合に属する

概要：Berger–Fresse §1.4.4 の行末側の逆対応を残余集合へ戻す。
方針：探索の停止行で選択する解放値を挿入点と同定し、延長行の長さを使う。
規約：成功出力の退化は許し、位置の所属を追加仮定しない。
使われ方：二種類の残余削除の全単射の逆写像の値域を保証する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：逆構成の挿入点は延長した行の内部にある（BF §1.4.4）。
方針：停止行で選択された解放値の座標を、唯一の後続出現と比較する。
規約：最終末尾の延長も同じ所属範囲で扱う。
使われ方：長い行の位置として挿入点を一文字行の集合から分離する。 -/
lemma point_in_late_row (b : ReverseTransferData w r out q) :
    let r' := deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long
    scheduleOffset r' b.late ≤ b.point.val ∧
      b.point.val < scheduleOffset r' b.late + (r'.val b.late).val := by
  let r' := deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long
  let before := b.context.before ++
    (vertexRow w b.early.castSucc, (r.val b.early.castSucc).val - 1) :: b.earlier
  let picked := b.context.picked ++
    (available b.context.removed (vertexRow w b.early.castSucc)).take
      ((r.val b.early.castSucc).val - 1) :: b.selected
  have he : rows w r' = before ++
      (vertexRow w b.late, (r.val b.late).val + 1) :: b.later := by
    simpa only [before, List.append_assoc, List.cons_append] using b.changed_rows
  have hp : ExtractionPrefix before [] picked b.finish := b.to_chosen_prefix
  have hlen : before.length = b.late.val := by
    simp only [before, List.length_append, List.length_cons]
    have := b.late_index
    omega
  have hstart : picked.flatten.length = scheduleOffset r' b.late :=
    hp.output_length.trans (rows_prefix_sum w r' before _ he b.late hlen)
  have hsuccess : reduceRows (before ++
      (vertexRow w b.late, (r.val b.late).val + 1) :: b.later) [] = some b.new := by
    rw [← he]
    exact b.success
  obtain ⟨tail, htail, hout⟩ := hp.split_success _ _ hsuccess
  obtain ⟨_, hb, post, _, htailOut⟩ := reduceRows_cons_success _ _ _ _ _ htail
  have hselect : b.a ∈ (available b.finish (vertexRow w b.late)).take
      ((r.val b.late).val + 1) := by
    have hs := b.search.selection_cases
    rw [b.chosen_eq] at hs
    rcases hs with hm | ⟨_, _, hm⟩
    · obtain ⟨i, hi, hv⟩ := List.mem_take_iff_getElem.mp hm
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, hv⟩
    · exact hm
  obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp hselect
  let selected := (available b.finish (vertexRow w b.late)).take ((r.val b.late).val + 1)
  have hjSelected : j < selected.length := hj
  have hshape : b.new = picked.flatten ++ (selected ++ post) := by
    rw [hout, htailOut]
  have hnewLen := congrArg List.length hshape
  simp only [List.length_append] at hnewLen
  let k : Fin b.new.length := ⟨picked.flatten.length + j, by omega⟩
  have hkvalue : b.new[k.val] = b.a := by
    have ht := getElem_of_block_position b.new picked.flatten selected post hshape k
      ⟨j, hj⟩ (by rfl)
    exact ht.trans hv
  obtain ⟨_, hbound, _, _, _⟩ := reduceRows_cons_success _ _ _ _ _ b.context.success
  have hshort : ((available b.context.removed (vertexRow w b.early.castSucc)).take
      ((r.val b.early.castSucc).val - 1)).length = b.left.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
    exact b.left_length.symm
  have hlo : b.context.picked.flatten.length + b.left.length ≤ k.val := by
    change _ ≤ picked.flatten.length + j
    simp only [picked, List.flatten_append, List.flatten_cons, List.length_append]
    omega
  have hk := unique_insert_after_prefix b.new (b.context.picked.flatten ++ b.left)
    b.middle b.right b.a (by simpa only [List.append_assoc] using b.target_shape)
    b.absent_middle b.absent_right k (by simpa only [List.length_append] using hlo) hkvalue
  have hkp : k.val = b.point.val := by
    simp only [List.length_append] at hk
    have := b.point_value
    have := b.source_position
    omega
  have hslen : selected.length = (r.val b.late).val + 1 := by
    exact List.length_take_of_le hb
  have hrow : (r'.val b.late).val = (r.val b.late).val + 1 :=
    deletionScheduleTransfer_receiver _ _ _ _ _
  change scheduleOffset r' b.late ≤ b.point.val ∧
    b.point.val < scheduleOffset r' b.late + (r'.val b.late).val
  rw [← hstart, ← hkp, hrow, ← hslen]
  constructor
  · change picked.flatten.length ≤ picked.flatten.length + j
    omega
  · change picked.flatten.length + j < picked.flatten.length + selected.length
    omega

/-- 概要：逆構成の挿入点は一文字行の削除集合に属さない（BF §1.4.4）。
方針：実際の延長行の長さは 2 以上であり、挿入点はその行内にある。
規約：長さの証明項には依存しない。
使われ方：行末側から最終出現側の残余削除への写像の値域を与える。 -/
lemma point_not_singleton (b : ReverseTransferData w r out q)
    (hl : b.new.length = n + d) :
    b.point ∉ singletonPositions
      (deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long) b.new hl := by
  apply position_in_long_row_not_singleton _ b.late _ b.new hl b.point
    b.point_in_late_row.1 b.point_in_late_row.2
  rw [deletionScheduleTransfer_receiver]
  have := r.property.1 b.late
  omega

end ReverseTransferData

end SerrePositivity.EInfinity.TableReduction
