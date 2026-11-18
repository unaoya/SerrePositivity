module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CursorRowInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlockIntervalOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockCursorStates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalSourceRows

/-!
模型。文献の定義との比較は後で
# 任意の二つの元の行内位置の間の抽出証跡

概要：Berger–Fresse §1.5.7 の成分の始終点の間を元の成功表から切り出す。
方針：同じ行か異なる行かで分け、両端の状態を元の cursor の状態へそろえる。
規約：両端の文字を含み、元の置換行の順序と終点前の除外状態を保持する。
使われ方：内側の任意の重なる分割成分を実際の抽出証跡として構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の成功表の閉区間の語・状態・行数・元の行列を持つ証跡（BF §1.5.7）。
方針：一行内の証跡と二行間の証跡を、同じ元の端点状態でまとめる。
規約：終点の文字は次の除外状態へ加えない。
使われ方：成分の次数＋1 行の選択を元の shuffle の行列へ接続する。 -/
lemma cursorInterval_nonempty {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (i j : Fin (d + 1)) (hij : i ≤ j)
    (first : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v))
    (last : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r j (List.ofFn v)) (p q : Fin (n + d))
    (a : Fin (r.val i).val) (b : Fin (r.val j).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + a.val) (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j + b.val)
    (hpq : p ≤ q) :
    ∃ part selected,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix part
        (first.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available first.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take a.val) selected
        (last.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available last.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j)).take b.val) ∧
      selected.flatten = ((List.ofFn v).drop p.val).take (q.val - p.val + 1) ∧
      part.length = j.val - i.val + 1 ∧
      part.map Prod.fst = (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop i.val).take (j.val - i.val + 1)).map Prod.fst := by
  rcases eq_or_lt_of_le hij with he | hlt
  · subst j
    have hab : a ≤ b := by change a.val ≤ b.val; change p.val ≤ q.val at hpq; omega
    refine ⟨[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, b.val - a.val + 1)],
      [((List.ofFn v).drop p.val).take (q.val - p.val + 1)], ?_, ?_, ?_, ?_⟩
    · have ht := first.interval_prefix p q a b hp hq hab
      simpa only [last.removed_eq first] using ht
    · simp only [List.flatten_singleton]
    · simp only [List.length_cons, List.length_nil, Nat.sub_self, Nat.zero_add]
    · simpa only [List.map_cons, List.map_nil, Nat.sub_self, Nat.zero_add] using
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_interval_singleton w r i).symm
  · obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleBlock_nonempty w r i j hlt (List.ofFn v) h
    obtain ⟨selected, ht, hw, hl⟩ := c.interval_prefix_word p q a b hp hq
    let part := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, (r.val i).val - a.val) ::
      (c.middle ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, b.val + 1)])
    have htrace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix part
        (first.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available first.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take a.val) selected
        (last.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available last.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j)).take b.val) := by
      rw [c.receiver_removed_eq first, c.donor_removed_eq last] at ht
      exact ht
    refine ⟨part, selected, htrace, hw, ?_, ?_⟩
    · have hc : selected.length = part.length := by
        simpa only [List.length_map] using congrArg List.length htrace.lengths
      omega
    · exact c.interval_source_rows _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
