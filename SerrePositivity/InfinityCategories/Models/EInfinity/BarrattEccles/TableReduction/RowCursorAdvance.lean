module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixUniqueness

/-!
模型。文献の定義との比較は後で
# 元の成功表の隣接行の抽出状態の接続

概要：Berger–Fresse §1.5.7 の元の抽出 cursor を一行ずつ進める。
方針：現在行を先行証跡へ追加し、同じ先行行列の証跡の一意性で次行の状態と比較する。
規約：末尾以外の除外更新と選択行の連結は元の reduceRows と同じ。
使われ方：合成経路の水平・垂直移動で元の cursor を進める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

/-- 概要：cursor の先行行列は指定行の直前の take（BF §1.5.7）。
方針：元の行列の分割と先行行数を使う。
規約：任意の同じ行の証明書について成立する。
使われ方：隣接する二つの cursor の先行行列を同じ座標で比較する。 -/
lemma before_eq_take {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {out : List (Fin n)} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i out) :
    b.before = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val := by
  rw [b.split, ← b.before_length]
  simp only [List.take_left]

/-- 概要：次行の先行行列は現在行を加えた行列（BF §1.5.7）。
方針：隣接する take の差を実際の現在行の値で評価する。
規約：非最終行から次行への一段。
使われ方：現在行を元の先行抽出証跡の後へ追加する。 -/
lemma next_before {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} (i : Fin d)
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i.castSucc out) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i.succ out) :
    c.before = b.before ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val)] := by
  rw [c.before_eq_take, b.before_eq_take]
  have hi : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn]
    omega
  have hindex : (⟨i.val, by omega⟩ : Fin (d + 1)) = i.castSucc := Fin.ext rfl
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow, List.getElem_ofFn, Fin.val_succ, Fin.val_castSucc, hindex] using
    List.take_succ_eq_append_getElem hi

/-- 概要：隣接 cursor の除外状態は現在行の末尾以外を加える元の更新（BF §1.5.7）。
方針：現在行を先行証跡へ連結し、次行の証跡と一意性で照合する。
規約：選択行列の一致も同時に得る。
使われ方：合成経路の移動で元の成功表の抽出状態を実際に進める。 -/
lemma next_state {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} (i : Fin d)
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i.castSucc out) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i.succ out) :
    c.selectedBefore = b.selectedBefore ++
        [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take (r.val i.castSucc).val] ∧
      c.removed = b.removed ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take ((r.val i.castSucc).val - 1) := by
  have hone : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val)] b.removed
      [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take (r.val i.castSucc).val]
      (b.removed ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take ((r.val i.castSucc).val - 1)) :=
    .cons (r.property.1 i.castSucc) b.bound (.nil _)
  have hcombined := b.before_trace.trans hone
  have hc := c.before_trace
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor.next_before i b c] at hc
  exact hc.unique hcombined

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
