module

public import SerrePositivity.EInfinity.TableReduction.ScheduleBlock
public import SerrePositivity.EInfinity.TableReduction.RowInterval
public import SerrePositivity.EInfinity.TableReduction.PrefixExclusions

/-!
# 元の二つの行を端とする成分の抽出証跡

概要：Berger–Fresse §1.5.7 の始行内部から終行内部までの元の抽出を構成する。
方針：始行の残り・元の中間証跡・終行の先頭の証跡を連結する。
規約：両端の文字を含み、終点の文字自身は終状態へ除外しない。
使われ方：正の成分次数を持つ内側部分語の実際の抽出証跡。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction.ScheduleBlock

/-- 概要：異なる二行の内部を端とする閉区間の元の抽出証跡（BF §1.5.7）。
方針：始行の短縮区間を元の中間証跡と終行の短縮区間へ連結する。
規約：中間行が零個の場合も同じ構成。
使われ方：合成経路の一成分に対応する元の複数行を切り出す。 -/
lemma interval_prefix {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : Schedule n d} {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (c : ScheduleBlock w r receiver donor out)
    (a : Fin (r.val receiver).val) (b : Fin (r.val donor).val) :
    ExtractionPrefix
      ((vertexRow w receiver, (r.val receiver).val - a.val) ::
        (c.middle ++ [(vertexRow w donor, b.val + 1)]))
      (c.removed ++ (available c.removed (vertexRow w receiver)).take a.val)
      ((((available c.removed (vertexRow w receiver)).drop a.val).take
          ((r.val receiver).val - a.val)) ::
        (c.picked ++ [(available c.finish (vertexRow w donor)).take (b.val + 1)]))
      (c.finish ++ (available c.finish (vertexRow w donor)).take b.val) := by
  have hpos := r.property.1 receiver
  have ha := a.isLt
  have hfirst := rowInterval_prefix c.removed (vertexRow w receiver)
    (List.nodup_ofFn_ofInjective (w receiver).symm.injective) a.val ((r.val receiver).val - 1)
    (by omega) (by have := c.receiver_bound; omega)
  have he : (r.val receiver).val - 1 - a.val + 1 = (r.val receiver).val - a.val := by omega
  rw [he] at hfirst
  have hlast : ExtractionPrefix [(vertexRow w donor, b.val + 1)] c.finish
      [(available c.finish (vertexRow w donor)).take (b.val + 1)]
      (c.finish ++ (available c.finish (vertexRow w donor)).take b.val) := by
    have hb : b.val + 1 ≤ (available c.finish (vertexRow w donor)).length := by
      have := c.donor_bound; have := b.isLt; omega
    apply ExtractionPrefix.cons (by omega) hb
    simpa only [Nat.add_sub_cancel] using
      (ExtractionPrefix.nil (c.finish ++ (available c.finish (vertexRow w donor)).take b.val))
  exact hfirst.trans (c.middle_trace.trans hlast)

end SerrePositivity.EInfinity.TableReduction.ScheduleBlock
