module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionExponentDecomposition
public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerPositionExponent
public import SerrePositivity.EInfinity.SimplexCuts.CompositeInternalHeightBalance
public import SerrePositivity.EInfinity.SimplexCuts.InternalCaesuraIndicators

/-!
# 元の合成位置指数と内外位置指数の釣り合い

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
報告 §253・§289 の全和。各内部辺の同じ高さを区切りの有無で重み付けして足す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成位置指数は、同じ内外位置指数とB_i・区切り順位で釣り合う（BF §2.2.6）。 -/
lemma positiveComposite_positionExponent_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (_h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    positionExponent c.2 (positiveCompositeCutWord u v k c.1).val +
      (∑ i, Surjection.segmentDegree v.val c.1 i *
        Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i)) =
    positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
      positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
      (∑ i, Surjection.segmentDegree v.val c.1 i *
        positiveCompositeOtherActivePrefix u v k c i) := by
  let C (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin ((c.1.val i).val - 1)) : Prop :=
    Surjection.Caesura v.val ⟨c.1.start i + z.val, by
      have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
  let E (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin ((c.1.val i).val - 1)) :=
    hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i
      ⟨z.val, by have hz := z.isLt; omega⟩)
  let G (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin ((c.1.val i).val - 1)) :=
    hi c.2 (positiveCompositeSegmentPosition u v k c.1 i ⟨z.val, by have hz := z.isLt; omega⟩)
  let B := positiveCompositeOtherActivePrefix u v k c
  let R (i : Fin (Surjection.occurrenceCount u.val k)) :=
    Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i)
  let g := Surjection.segmentDegree v.val c.1
  have hsum (i : Fin (Surjection.occurrenceCount u.val k)) :
      (∑ z, if C i z then E i z else 0) + g i * B i =
        (∑ z, if C i z then G i z else 0) + g i * R i := by
    have hpoint (z : Fin ((c.1.val i).val - 1)) :
        (if C i z then E i z else 0) + (if C i z then 1 else 0) * B i =
          (if C i z then G i z else 0) + (if C i z then 1 else 0) * R i := by
      by_cases hz : C i z
      · simp only [hz, ↓reduceIte, one_mul]
        exact positiveComposite_segment_internal_height_balance u v k c i z
      · simp only [hz, ↓reduceIte, zero_mul, Nat.add_zero]
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ => hpoint z)
    have hc : (∑ z, if C i z then 1 else 0 : ℕ) = g i :=
      sum_internal_caesuraIndicators v.val c.1 i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, hc] at hs
    exact hs
  have ht := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hsum i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at ht
  have he : positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val =
      ∑ i, ∑ z, if C i z then E i z else 0 :=
    positiveComposite_inner_positionExponent_decomposition u v k c
  have hg : positionExponent c.2 (positiveCompositeCutWord u v k c.1).val =
      positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
        ∑ i, ∑ z, if C i z then G i z else 0 :=
    positiveComposite_positionExponent_decomposition u v k c
  change _ + (∑ i, g i * R i) = _ + _ + (∑ i, g i * B i)
  omega

end SerrePositivity.EInfinity.SimplexCuts
