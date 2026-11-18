module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowOwners
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PreviousOccurrenceGap

/-!
模型。文献の定義との比較は後で
# 二行の抽出の出力座標と削除値

概要：Berger–Fresse §1.4.4 の切り出した語を元の出力位置で照合する。
方針：先行部分の長さと行長から連結語の位置を計算する。
規約：退化出力も含む。
使われ方：受け取り行末の値・削除行内の値・中間行の不出現を同時に確保する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：連結語のブロック内の位置を同じ有限添字で評価する（BF §1.4.4）。
方針：リストの等式による評価を連結の評価公式へ移す。
規約：語と添字の長さの証明項を保持する。
使われ方：Schedule の位置から切り出した語の値へ移る。 -/
lemma getElem_of_block_position {α : Type*} (out pre row post : List α)
    (he : out = pre ++ (row ++ post)) (k : Fin out.length) (j : Fin row.length)
    (hk : k.val = pre.length + j.val) : out[k.val] = row[j.val] := by
  refine (List.getElem_of_eq he k.isLt).trans ?_
  simpa only [hk] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_inside_row pre row post j

namespace ScheduleBlock

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
  {receiver donor : Fin (d + 1)} {out : List (Fin n)}

/-- 概要：受け取り行末の元の出力値は利用可能行の末尾の選択値（BF §1.4.4）。
方針：開始位置と行長から末尾の添字を行内に直す。
規約：末尾位置は p+1＝開始位置＋行長で指定する。
使われ方：直前出現の値が受け取り行の実際の末尾であることを示す。 -/
lemma receiver_end_value (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (p : Fin out.length)
    (hp : p.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + (r.val receiver).val) :
    out[p.val] = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver))[(r.val receiver).val - 1]'(by
      have := r.property.1 receiver; have := b.receiver_bound; omega) := by
  let j : Fin ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val).length :=
    ⟨(r.val receiver).val - 1, by rw [b.receiver_take_length]; have := r.property.1 receiver; omega⟩
  have hpos : p.val = b.selectedBefore.flatten.length + j.val := by
    have := b.prefix_length
    have := r.property.1 receiver
    dsimp only [j]
    omega
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out b.selectedBefore.flatten
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val)
    (b.picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++
      b.tail)) b.output_eq p j hpos
  exact he.trans (List.getElem_take)

/-- 概要：削除行の元の出力値は利用可能行の対応する行内値（BF §1.4.4）。
方針：行開始位置を引いて行内添字を作る。
規約：所属範囲を両側の不等号で指定する。
使われ方：削除値で利用可能語を前後に分ける。 -/
lemma donor_value (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (k : Fin out.length)
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val)
    (hh : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor))[k.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor]'(by
      have := b.donor_bound; omega) = out[k.val] := by
  let pre := b.selectedBefore.flatten ++
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val ++ b.picked.flatten)
  have hpre : pre.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor := by
    simp only [pre, List.length_append, b.receiver_take_length]
    have := b.donor_start
    omega
  let j : Fin ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val).length :=
    ⟨k.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor, by rw [b.donor_take_length]; omega⟩
  have he : out = pre ++
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++ b.tail) := by
    simpa only [pre, List.append_assoc] using b.output_eq
  have hpos : k.val = pre.length + j.val := by dsimp only [j]; omega
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out pre
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val) b.tail he k j hpos
  exact (hv.trans List.getElem_take).symm

/-- 概要：直前出現と削除行の間の抽出語に削除値はない（BF §1.4.4）。
方針：中間語の各所属を直前出現と現在位置の間の有限添字へ直す。
規約：削除位置は削除行の開始位置以降。
使われ方：中間行の早い除外の輸送に不出現条件を供給する。 -/
lemma previousOccurrence_not_mem_middle (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out)
    (k : Fin out.length)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val +
      1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + (r.val receiver).val)
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val) : out[k.val] ∉ b.picked.flatten := by
  intro hx
  obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp hx
  let p := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp
  have hstart := b.donor_start
  have hbefore := b.prefix_length
  let q : Fin out.length := ⟨b.selectedBefore.flatten.length + (r.val receiver).val + j, by
    have := k.isLt; omega⟩
  let pre := b.selectedBefore.flatten ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val
  have hpre : pre.length = b.selectedBefore.flatten.length + (r.val receiver).val := by
    simp only [pre, List.length_append, b.receiver_take_length]
  have hshape : out = pre ++
      (b.picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++
        b.tail)) := by
    simpa only [pre, List.append_assoc] using b.output_eq
  have hqval : out[q.val] = out[k.val] := by
    have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out pre b.picked.flatten
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++ b.tail)
      hshape q ⟨j, hj⟩ (by dsimp only [q]; omega)
    exact hh.trans hv
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrence_no_between
    (fun j : Fin out.length => out[j.val]) k hp q _ _ hqval
  · change p.val < b.selectedBefore.flatten.length + (r.val receiver).val + j
    omega
  · change b.selectedBefore.flatten.length + (r.val receiver).val + j < k.val
    omega

end ScheduleBlock

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
