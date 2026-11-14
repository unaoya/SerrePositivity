module

public import SerrePositivity.EInfinity.SimplexCuts.ConsecutiveCaesuraCounts

/-!
# 同じ部分語の内部区切りを成分次数で読む

Berger–Fresse §1.2.5・§2.2.6、M14 L12a の C452。
報告 §289 の同じ有限位置・同じ順位の証明分割。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 内部位置の区切りの総数は元の成分次数（BF §1.2.5）。 -/
lemma sum_internal_caesuraIndicators {r t n e : ℕ}
    (w : Fin ((n + 1) + e) → Fin r)
    (o : Surjection.OverlapPartition t ((n + 1) + e)) (i : Fin t) :
    (∑ z : Fin ((o.val i).val - 1), if Surjection.Caesura w
      ⟨o.start i + z.val, by have hb := o.start_add_length_le i; have hz := z.isLt; omega⟩
      then 1 else 0 : ℕ) = Surjection.segmentDegree w o i := by
  have hlen := o.positive (by omega : 0 < (n + 1) + e) i
  have hc := sum_consecutive_caesuraIndicators w (o.start i) ((o.val i).val - 1)
    (by have hb := o.start_add_length_le i; omega)
  have he : o.start i + ((o.val i).val - 1) = o.start i + (o.val i).val - 1 := by omega
  have hr := congrArg (Surjection.lineRank w) he
  unfold Surjection.segmentDegree
  omega

end SerrePositivity.EInfinity.SimplexCuts
