module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixExclusions

/-!
模型。文献の定義との比較は後で
# 元の二つの行を端とする成分の抽出証跡

概要：Berger–Fresse §1.5.7 の始行内部から終行内部までの元の抽出を構成する。
方針：始行の残り・元の中間証跡・終行の先頭の証跡を連結する。
規約：両端の文字を含み、終点の文字自身は終状態へ除外しない。
使われ方：正の成分次数を持つ内側部分語の実際の抽出証跡。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock

/-- 概要：異なる二行の内部を端とする閉区間の元の抽出証跡（BF §1.5.7）。
方針：始行の短縮区間を元の中間証跡と終行の短縮区間へ連結する。
規約：中間行が零個の場合も同じ構成。
使われ方：合成経路の一成分に対応する元の複数行を切り出す。 -/
lemma interval_prefix {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out)
    (a : Fin (r.val receiver).val) (b : Fin (r.val donor).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val - a.val) ::
        (c.middle ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, b.val + 1)]))
      (c.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take a.val)
      ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).drop a.val).take
          ((r.val receiver).val - a.val)) ::
        (c.picked ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (b.val + 1)]))
      (c.finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take b.val) := by
  have hpos := r.property.1 receiver
  have ha := a.isLt
  have hfirst := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowInterval_prefix c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)
    (List.nodup_ofFn_ofInjective (w receiver).symm.injective) a.val ((r.val receiver).val - 1)
    (by omega) (by have := c.receiver_bound; omega)
  have he : (r.val receiver).val - 1 - a.val + 1 = (r.val receiver).val - a.val := by omega
  rw [he] at hfirst
  have hlast : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, b.val + 1)] c.finish
      [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (b.val + 1)]
      (c.finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take b.val) := by
    have hb : b.val + 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).length := by
      have := c.donor_bound; have := b.isLt; omega
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.cons (by omega) hb
    simpa only [Nat.add_sub_cancel] using
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.nil (c.finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take b.val))
  exact hfirst.trans (c.middle_trace.trans hlast)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock
