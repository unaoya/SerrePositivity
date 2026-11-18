module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorAdvance

/-!
模型。文献の定義との比較は後で
# 二行の分割と各行 cursor の元の状態の一致

概要：Berger–Fresse §1.5.7 の区間の両端で異なる取り出し方の元の除外状態を照合する。
方針：同じ先行行列の抽出証跡の一意性を使う。
規約：除外状態はリストの等式で一致する。
使われ方：二行間の区間証跡を語の位置から決まる cursor へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：同じ行を指す二つの cursor の元の除外状態は一致（BF §1.5.7）。
方針：先行行列を同じ take へ戻し、その証跡の一意性を適用する。
規約：証明書の選択に依存しない。
使われ方：同じ行内の二端点の除外状態を比較する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor.removed_eq {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {i : Fin (d + 1)}
    {out : List (Fin n)} (b c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i out) : b.removed = c.removed := by
  have hb := b.before_trace
  rw [b.before_eq_take, ← c.before_eq_take] at hb
  exact (hb.unique c.before_trace).2

namespace ScheduleBlock

/-- 概要：二行分割の始行直前の状態は元の同じ行 cursor と一致（BF §1.5.7）。
方針：二つの先行行列を指定行までの take に同定する。
規約：元の証明書の選択に依存しない。
使われ方：複数行区間の初期状態を位置で指定された状態へ移す。 -/
lemma receiver_removed_eq {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r receiver out) :
    c.removed = b.removed := by
  have hbefore : c.before = b.before := by
    rw [b.before_eq_take, c.split, ← c.before_length]
    simp only [List.take_left]
  have hc := c.before_trace
  rw [hbefore] at hc
  exact (hc.unique b.before_trace).2

/-- 概要：二行分割の終行直前の状態は元の同じ行 cursor と一致（BF §1.5.7）。
方針：始行と中間行の証跡を先行証跡へ連結し、終行 cursor と比較する。
規約：中間行数零も含む。
使われ方：複数行区間の終状態を位置で指定された状態へ移す。 -/
lemma donor_removed_eq {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r donor out) :
    c.finish = b.removed := by
  let pre := c.before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) :: c.middle
  have hsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = pre ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: c.after := by
    simpa only [pre, List.append_assoc, List.cons_append] using c.split
  have hlen : pre.length = donor.val := by
    simp only [pre, List.length_append, List.length_cons]
    have := c.middle_length
    omega
  have hpre : pre = b.before := by
    rw [b.before_eq_take, hsplit, ← hlen]
    simp only [List.take_left]
  have htrace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix pre []
      (c.selectedBefore ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take
        (r.val receiver).val :: c.picked) c.finish :=
    c.before_trace.trans (.cons (r.property.1 receiver) c.receiver_bound c.middle_trace)
  rw [hpre] at htrace
  exact (htrace.unique b.before_trace).2

end ScheduleBlock

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
