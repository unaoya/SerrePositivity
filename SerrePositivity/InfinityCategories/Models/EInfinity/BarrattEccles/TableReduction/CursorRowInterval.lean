module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorRemainder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowInterval

/-!
模型。文献の定義との比較は後で
# 同じ元の抽出行に含まれる成分

概要：Berger–Fresse §1.5.7 の始終点が同じ行にある成分を元の語の閉区間として抽出する。
方針：行内再開の出力を終点まで take し、一行内区間の先行証跡へ移す。
規約：両端は同じ元の行内座標で指定する。
使われ方：次数零の内側成分を追加の成功仮定なしに構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

/-- 概要：同じ行の二点間の元の語は利用可能行の同じ閉区間（BF §1.5.7）。
方針：始点からの出力末尾を終点まで切り、現在行の範囲内で take を合成する。
規約：両端を含める。
使われ方：一行の選択区間と実際の分割部分語を同定する。 -/
lemma interval_output {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p q : Fin (n + d))
    (a b : Fin (r.val i).val) (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + a.val)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + b.val) (hab : a ≤ b) :
    ((List.ofFn v).drop p.val).take (q.val - p.val + 1) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop a.val).take (b.val - a.val + 1) := by
  have hlength : q.val - p.val + 1 = b.val - a.val + 1 := by omega
  have hb : b.val - a.val + 1 ≤ (r.val i).val - a.val := by
    have := b.isLt; omega
  have hbound : b.val - a.val + 1 ≤
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop a.val).take
        ((r.val i).val - a.val)).length := by
    simp only [List.length_take, List.length_drop]
    have := c.bound; have := b.isLt
    omega
  calc
    _ = ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop a.val).take
        ((r.val i).val - a.val)) ++ c.tail).take (q.val - p.val + 1) :=
      congrArg (List.take (q.val - p.val + 1)) (c.output_drop p a hp)
    _ = _ := by
      rw [hlength, List.take_append_of_le_length hbound, List.take_take, Nat.min_eq_left hb]

/-- 概要：同じ行内の閉区間の実際の語を抽出する証跡（BF §1.5.7）。
方針：一行の区間抽出の出力を元の語の指定区間へ照合する。
規約：終点の文字より前だけを終状態へ除外する。
使われ方：共有端点を持つ一行成分を元の成功表から作る。 -/
lemma interval_prefix {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p q : Fin (n + d))
    (a b : Fin (r.val i).val) (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + a.val)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + b.val) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, b.val - a.val + 1)]
      (c.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take a.val)
      [((List.ofFn v).drop p.val).take (q.val - p.val + 1)]
      (c.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take b.val) := by
  rw [c.interval_output p q a b hp hq hab]
  have hb : b.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length := by
    have := c.bound; have := b.isLt; omega
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowInterval_prefix c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)
    (List.nodup_ofFn_ofInjective (w i).symm.injective) a.val b.val hab hb

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
