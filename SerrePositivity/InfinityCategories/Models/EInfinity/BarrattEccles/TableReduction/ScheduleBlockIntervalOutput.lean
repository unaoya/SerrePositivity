module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlockInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalBlockWords

/-!
模型。文献の定義との比較は後で
# 複数行成分の抽出出力と元の語の区間

概要：Berger–Fresse §1.5.7 の複数行の成分証跡の出力を元の語の閉区間へ同定する。
方針：元の五部分の出力表示を始点で drop し、終点までの長さで take する。
規約：両端を含め、中間行の出力は全て保持する。
使われ方：内側の重なる分割の各部分語を元の成功抽出へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock

/-- 概要：異なる二行を端とする選択語は元の語の同じ閉区間（BF §1.5.7）。
方針：元の出力の前半を除き、三ブロックの区間公式で終行先頭まで切り出す。
規約：始終点の行内座標は元の Schedule のもの。
使われ方：複数行の成分証跡の平坦化を実際の部分語へ移す。 -/
lemma interval_output {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {receiver donor : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor (List.ofFn v)) (p q : Fin (n + d))
    (a : Fin (r.val receiver).val) (b : Fin (r.val donor).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + a.val)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + b.val) :
    ((List.ofFn v).drop p.val).take (q.val - p.val + 1) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).drop a.val).take
        ((r.val receiver).val - a.val) ++
      (c.picked.flatten ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (b.val + 1)) := by
  have ha : a.val ≤ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take
      (r.val receiver).val).length := by rw [c.receiver_take_length]; exact Nat.le_of_lt a.isLt
  have hb : b.val + 1 ≤ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take
      (r.val donor).val).length := by rw [c.donor_take_length]; have := b.isLt; omega
  have hb' : b.val + 1 ≤ (r.val donor).val := by have := b.isLt; omega
  have hlen : q.val - p.val + 1 = (r.val receiver).val - a.val +
      c.picked.flatten.length + (b.val + 1) := by
    have hstart := c.donor_start
    have hprefix := c.prefix_length
    have := a.isLt
    omega
  calc
    _ = ((c.selectedBefore.flatten ++
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val ++
          (c.picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take
            (r.val donor).val ++ c.tail)))).drop p.val).take (q.val - p.val + 1) :=
      congrArg (fun xs => (xs.drop p.val).take (q.val - p.val + 1)) c.output_eq
    _ = ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val) ++
        (c.picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take
          (r.val donor).val ++ c.tail))).drop a.val).take (q.val - p.val + 1) := by
      rw [hp, ← c.prefix_length, List.drop_length_add_append]
    _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val).drop a.val ++
        (c.picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take
          (r.val donor).val).take (b.val + 1)) := by
      rw [hlen]
      simpa only [c.receiver_take_length] using
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.interval_of_three_blocks _ _ _ _ a.val (b.val + 1) ha hb
    _ = _ := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left hb']

/-- 概要：複数行区間の証跡は元の部分語と正しい行数を持つ（BF §1.5.7）。
方針：連結した選択行の平坦化と中間行数を元の位置差へ照合する。
規約：行数は元の終行番号−始行番号＋1。
使われ方：成分次数＋1 行の元の成功証跡を合成経路へ渡す。 -/
lemma interval_prefix_word {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {receiver donor : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor (List.ofFn v)) (p q : Fin (n + d))
    (a : Fin (r.val receiver).val) (b : Fin (r.val donor).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + a.val)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + b.val) :
    ∃ selected,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val - a.val) ::
          (c.middle ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, b.val + 1)]))
        (c.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take a.val) selected
        (c.finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take b.val) ∧
      selected.flatten = ((List.ofFn v).drop p.val).take (q.val - p.val + 1) ∧
      selected.length = donor.val - receiver.val + 1 := by
  refine ⟨_, c.interval_prefix a b, ?_, ?_⟩
  · simpa only [List.flatten_cons, List.flatten_append, List.flatten_singleton,
      List.flatten_nil, List.append_nil] using
      (c.interval_output p q a b hp hq).symm
  · have hlength : c.picked.length = c.middle.length := by
      simpa only [List.length_map] using congrArg List.length c.middle_trace.lengths
    simp only [List.length_cons, List.length_append, List.length_nil]
    have hmiddle := c.middle_length
    have hbefore := c.before_length
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock
