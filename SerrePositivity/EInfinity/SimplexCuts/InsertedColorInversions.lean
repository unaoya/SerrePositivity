module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorCrossOrder
public import SerrePositivity.EInfinity.SimplexCuts.WeightedVertexInversions

/-!
# 指定した挿入色の順序同値による逆転対の有限和

Berger–Fresse §2.2.6、M14 L12a の C452。
同じ活動頂点の対の寄与を比較し、既存の色別同値で二重和を再添字付けする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ挿入色の活動頂点対の逆転寄与は内側と一致（BF §2.2.6）。 -/
lemma insertedColorPathOrderIso_active_inversionTerm {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b b' : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)))
    (y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b'))) :
    (if x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val ∧
        y.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val then
      IntervalCuts.positionInversionTerm (label c.2 (positiveCompositeCutWord u v k c.1).val)
        x.val y.val else 0) =
    (if (insertedColorPathOrderIso u v k c b x).val ∈
          activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val ∧
        (insertedColorPathOrderIso u v k c b' y).val ∈
          activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val then
      IntervalCuts.positionInversionTerm
        (label (positiveCompositeInnerCut u v k c) (positiveWord v).val)
        (insertedColorPathOrderIso u v k c b x).val
        (insertedColorPathOrderIso u v k c b' y).val else 0) := by
  have hx := (Finset.mem_filter.mp x.property).2
  have hy := (Finset.mem_filter.mp y.property).2
  have hx' := (Finset.mem_filter.mp (insertedColorPathOrderIso u v k c b x).property).2
  have hy' := (Finset.mem_filter.mp (insertedColorPathOrderIso u v k c b' y).property).2
  have hc : BarrattEccles.insertedPosition m (n + 1) k b' <
      BarrattEccles.insertedPosition m (n + 1) k b ↔ b' < b := by
    change k.val + b'.val < k.val + b.val ↔ b'.val < b.val
    omega
  simp only [insertedColorPathOrderIso_active_iff]
  congr 1
  unfold IntervalCuts.positionInversionTerm
  simp only [hx, hy, hx', hy', insertedColorPathOrderIso_cross_lt_iff, hc]

/-- 同じ色別同値で数えた活動逆転対の二重和は内側と一致（BF §2.2.6）。 -/
lemma insertedColorPathOrderIso_active_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b b' : Fin (n + 1)) :
    (∑ x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.insertedPosition m (n + 1) k b)),
      ∑ y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.insertedPosition m (n + 1) k b')),
      if x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val ∧
          y.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val then
        IntervalCuts.positionInversionTerm (label c.2 (positiveCompositeCutWord u v k c.1).val)
          x.val y.val else 0) =
    (∑ x : ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b),
      ∑ y : ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b'),
      if x.val ∈ activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val ∧
          y.val ∈ activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val
        then IntervalCuts.positionInversionTerm
          (label (positiveCompositeInnerCut u v k c) (positiveWord v).val) x.val y.val else 0) := by
  apply Fintype.sum_equiv (insertedColorPathOrderIso u v k c b).toEquiv
  intro x
  apply Fintype.sum_equiv (insertedColorPathOrderIso u v k c b').toEquiv
  intro y
  exact insertedColorPathOrderIso_active_inversionTerm u v k c b b' x y

end SerrePositivity.EInfinity.SimplexCuts
