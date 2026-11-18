module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseRowPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowInterior
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.UniqueInsertion

/-!
模型。文献の定義との比較は後で
# 逆構成の挿入点は残余削除集合に属する

概要：Berger–Fresse §1.4.4 の行末側の逆対応を残余集合へ戻す。
方針：探索の停止行で選択する解放値を挿入点と同定し、延長行の長さを使う。
規約：成功出力の退化は許し、位置の所属を追加仮定しない。
使われ方：二種類の残余削除の全単射の逆写像の値域を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：逆構成の挿入点は延長した行の内部にある（BF §1.4.4）。
方針：停止行で選択された解放値の座標を、唯一の後続出現と比較する。
規約：最終末尾の延長も同じ所属範囲で扱う。
使われ方：長い行の位置として挿入点を一文字行の集合から分離する。 -/
lemma point_in_late_row (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    let r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' b.late ≤ b.point.val ∧
      b.point.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' b.late + (r'.val b.late).val := by
  let r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long
  let before := b.context.before ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val - 1) :: b.earlier
  let picked := b.context.picked ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.context.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc)).take
      ((r.val b.early.castSucc).val - 1) :: b.selected
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r' = before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late, (r.val b.late).val + 1) :: b.later := by
    simpa only [before, List.append_assoc, List.cons_append] using b.changed_rows
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before [] picked b.finish := b.to_chosen_prefix
  have hlen : before.length = b.late.val := by
    simp only [before, List.length_append, List.length_cons]
    have := b.late_index
    omega
  have hstart : picked.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' b.late :=
    hp.output_length.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r' before _ he b.late hlen)
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late, (r.val b.late).val + 1) :: b.later) [] = some b.new := by
    rw [← he]
    exact b.success
  obtain ⟨tail, htail, hout⟩ := hp.split_success _ _ hsuccess
  obtain ⟨_, hb, post, _, htailOut⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ htail
  have hselect : b.a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late)).take
      ((r.val b.late).val + 1) := by
    have hs := b.search.selection_cases
    rw [b.chosen_eq] at hs
    rcases hs with hm | ⟨_, _, hm⟩
    · obtain ⟨i, hi, hv⟩ := List.mem_take_iff_getElem.mp hm
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, hv⟩
    · exact hm
  obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp hselect
  let selected := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late)).take ((r.val b.late).val + 1)
  have hjSelected : j < selected.length := hj
  have hshape : b.new = picked.flatten ++ (selected ++ post) := by
    rw [hout, htailOut]
  have hnewLen := congrArg List.length hshape
  simp only [List.length_append] at hnewLen
  let k : Fin b.new.length := ⟨picked.flatten.length + j, by omega⟩
  have hkvalue : b.new[k.val] = b.a := by
    have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position b.new picked.flatten selected post hshape k
      ⟨j, hj⟩ (by rfl)
    exact ht.trans hv
  obtain ⟨_, hbound, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ b.context.success
  have hshort : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.context.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc)).take
      ((r.val b.early.castSucc).val - 1)).length = b.left.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
    exact b.left_length.symm
  have hlo : b.context.picked.flatten.length + b.left.length ≤ k.val := by
    change _ ≤ picked.flatten.length + j
    simp only [picked, List.flatten_append, List.flatten_cons, List.length_append]
    omega
  have hk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.unique_insert_after_prefix b.new (b.context.picked.flatten ++ b.left)
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
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver _ _ _ _ _
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' b.late ≤ b.point.val ∧
    b.point.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' b.late + (r'.val b.late).val
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
lemma point_not_singleton (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q)
    (hl : b.new.length = n + d) :
    b.point ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long) b.new hl := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.position_in_long_row_not_singleton _ b.late _ b.new hl b.point
    b.point_in_late_row.1 b.point_in_late_row.2
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver]
  have := r.property.1 b.late
  omega

end ReverseTransferData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
