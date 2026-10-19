module

public import SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor
public import SerrePositivity.EInfinity.TableReduction.ReductionColumns
public import SerrePositivity.EInfinity.TableReduction.BlockCoordinates

/-!
# 元の出力位置と利用可能な行の値の一致

概要：Berger–Fresse §1.5.7 の成分端点の文字を元の抽出状態の行内値へ移す。
方針：同じ成功から得た先行部分長と選択行の長さを連結語の評価に使う。
規約：行末でも内部でも同じ評価公式を使う。
使われ方：指定値の前後の利用可能行を実際の語の値で分割する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

namespace ScheduleRowCursor

/-- 概要：指定出力位置の値は元の利用可能行の同じ行内位置の値（BF §1.5.7）。
方針：出力の三ブロック表示を行内添字で評価する。
規約：行内位置は選択行長の有限添字。
使われ方：合成の指定値が元の現在行のどの位置にあるかを確定する。 -/
lemma value {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = scheduleOffset r i + j.val) :
    v p = (available b.removed (vertexRow w i))[j.val]'(by
      have := b.bound; have := j.isLt; omega) := by
  let k : Fin (List.ofFn v).length := ⟨p.val, by simpa only [List.length_ofFn] using p.isLt⟩
  let q : Fin ((available b.removed (vertexRow w i)).take (r.val i).val).length :=
    ⟨j.val, by rw [List.length_take, Nat.min_eq_left b.bound]; exact j.isLt⟩
  have hpos : k.val = b.selectedBefore.flatten.length + q.val := by
    simpa only [k, q, b.prefix_length] using hp
  have hv := getElem_of_block_position (List.ofFn v) b.selectedBefore.flatten
    ((available b.removed (vertexRow w i)).take (r.val i).val) b.tail b.output_eq k q hpos
  simpa only [List.getElem_ofFn, List.getElem_take] using hv

/-- 概要：語から決まる行内添字での元の利用可能行の値（BF §1.5.7）。
方針：既存の reductionRow・reductionColumn の座標等式を一行の評価に渡す。
規約：元の成功証明を使って行と列を固定する。
使われ方：成分端点の値を追加仮定なしに利用可能行へ移す。 -/
lemma reductionColumn_value {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : Schedule n d} {v : Fin (n + d) → Fin n}
    (h : reduceRows (rows w r) [] = some (List.ofFn v)) (p : Fin (n + d))
    (b : ScheduleRowCursor w r (reductionRow w r v h p) (List.ofFn v)) :
    v p = (available b.removed (vertexRow w (reductionRow w r v h p)))[
      (reductionColumn w r v h p).val]'(by
        have := b.bound; have := (reductionColumn w r v h p).isLt; omega) :=
  b.value p (reductionColumn w r v h p) (reductionColumn_position w r v h p)

end ScheduleRowCursor

end SerrePositivity.EInfinity.TableReduction
