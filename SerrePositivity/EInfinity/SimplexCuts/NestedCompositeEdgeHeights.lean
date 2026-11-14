module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeEdgeEnumeration
public import SerrePositivity.EInfinity.SimplexCuts.NestedInnerHeightBounds

/-!
# 元の二段切断による合成語の全辺の高さ

Berger–Fresse §2.2.6、M14 L12a の逆復元。
元の境界と内部辺に同じ高さを指定し、その混合した順序を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ全辺の有限列挙を全単射として読む記法（BF §2.2.6）。 -/
def compositeEdgeEquiv {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    (Fin (m + d) ⊕ Fin (n + e)) ≃ Fin (m + n + (d + e)) :=
  Equiv.ofBijective _ (compositeEdgeSum_bijective u v k r)

/-- 元の外側境界の高さと、同じverticesで読む内側高さ（BF §2.2.6）。 -/
def positiveNestedEdgeHeight {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (_v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u _v k q) :
    Fin (m + d) ⊕ Fin (n + e) → Fin (q + 1) :=
  Sum.elim (cutHeights c.1) (fun a => vertices c.1 (positiveWord u) k (cutHeights c.2 a))

/-- C432：同じ全辺の位置順序は、元の二段切断の高さの順序を保つ（BF §2.2.6）。 -/
lemma positiveNestedEdgeHeight_mono {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (x y : Fin (m + d) ⊕ Fin (n + e))
    (h : compositeEdgeSum u v k (positiveNestedPartition u v k c) x ≤
      compositeEdgeSum u v k (positiveNestedPartition u v k c) y) :
    positiveNestedEdgeHeight u v k c x ≤ positiveNestedEdgeHeight u v k c y := by
  let r := positiveNestedPartition u v k c
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      exact (cutHeights c.1).monotone ((compositeOuterEdge_strictMono u v k r).le_iff_le.mp h)
    | inr a =>
      let p := positiveOccurrencePosition u k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)
      have hp : i.val < p.val := by
        by_contra hnot
        have ho := (compositeInnerOuterEdge_order u v k r a i).1 (le_of_not_gt hnot)
        exact (not_le_of_gt ho) h
      have hb := positiveNestedInnerHeight_bounds u v k c a
      change hi c.1 i.castSucc ≤ (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val
      exact (hi_le_lo_of_lt c.1 i.castSucc p hp).trans hb.1
  | inr a =>
    cases y with
    | inl i =>
      let p := positiveOccurrencePosition u k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)
      have hp : p.val ≤ i.val := by
        by_contra hnot
        have ho := (compositeInnerOuterEdge_order u v k r a i).2 (lt_of_not_ge hnot)
        exact (not_le_of_gt ho) h
      have hb := positiveNestedInnerHeight_bounds u v k c a
      change (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val ≤ hi c.1 i.castSucc
      exact hb.2.trans (hi_monotone c.1 (show p ≤ i.castSucc from hp))
    | inr b =>
      exact (vertices c.1 (positiveWord u) k).monotone
        ((cutHeights c.2).monotone ((compositeInnerEdge_strictMono u v k r).le_iff_le.mp h))

end SerrePositivity.EInfinity.SimplexCuts
