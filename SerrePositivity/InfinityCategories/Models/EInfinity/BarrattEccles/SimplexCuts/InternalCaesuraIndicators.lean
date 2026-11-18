module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ConsecutiveCaesuraCounts

/-!
模型。文献の定義との比較は後で
# 同じ部分語の内部区切りを成分次数で読む

Berger–Fresse §1.2.5・§2.2.6、M14 L12a の C452。
報告 §289 の同じ有限位置・同じ順位の証明分割。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 内部位置の区切りの総数は元の成分次数（BF §1.2.5）。 -/
lemma sum_internal_caesuraIndicators {r t n e : ℕ}
    (w : Fin ((n + 1) + e) → Fin r)
    (o : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t ((n + 1) + e)) (i : Fin t) :
    (∑ z : Fin ((o.val i).val - 1), if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura w
      ⟨o.start i + z.val, by have hb := o.start_add_length_le i; have hz := z.isLt; omega⟩
      then 1 else 0 : ℕ) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree w o i := by
  have hlen := o.positive (by omega : 0 < (n + 1) + e) i
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_consecutive_caesuraIndicators w (o.start i) ((o.val i).val - 1)
    (by have hb := o.start_add_length_le i; omega)
  have he : o.start i + ((o.val i).val - 1) = o.start i + (o.val i).val - 1 := by omega
  have hr := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank w) he
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
