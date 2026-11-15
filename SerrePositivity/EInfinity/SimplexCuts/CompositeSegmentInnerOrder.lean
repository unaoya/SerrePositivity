module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorPathMapSurjective

/-!
# 元の挿入頂点の順序は同じ内側経路で保たれる

Berger–Fresse §2.2.6、M14 L12a のC451。
同じ部分語では座標和の平行移動、異なる部分語では元の境界と色別順位を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成経路の順序は、指定した同じ内側頂点の順序を保つ（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_strict_order {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w) (hxy : x < y) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx <
      positiveCompositeSegmentInnerVertex u v k c j w y hy := by
  have hij : i ≤ j := by
    by_contra hn
    have hlt : j < i := lt_of_not_ge hn
    have hp : (positiveCompositeSegmentPosition u v k c.1 j w).val <
        (positiveCompositeSegmentPosition u v k c.1 i z).val :=
      IntervalCuts.compositeSegmentPosition_lt u v k c.1 j i hlt w z
    have hs := c.2.horizontal.monotone hxy.le
    rw [hx, hy] at hs
    have hval : (positiveCompositeSegmentPosition u v k c.1 i z).val ≤
        (positiveCompositeSegmentPosition u v k c.1 j w).val := hs
    omega
  rcases eq_or_lt_of_le hij with he | hlt
  · subst j
    have hsx := c.2.coordinate_sum x
    have hsy := c.2.coordinate_sum y
    rw [hx] at hsx
    rw [hy] at hsy
    change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val +
      z.val + (c.2.vertical x).val = x.val at hsx
    change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val +
      w.val + (c.2.vertical y).val = y.val at hsy
    have hbx := (positiveCompositeSegment_outer_bounds u v k c i z x hx).1
    have hby := (positiveCompositeSegment_outer_bounds u v k c i w y hy).1
    let first := (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)).val
    change (c.1.start i + z.val) +
        (first + ((c.2.vertical x).val -
          lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i))) <
      (c.1.start i + w.val) +
        (first + ((c.2.vertical y).val -
          lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i)))
    have hval : x.val < y.val := hxy
    omega
  · have hm1 := positiveCompositeSegmentVertexRank_mem u v k c i z x hx
    have hm2 := positiveCompositeSegmentVertexRank_mem u v k c j w y hy
    have hrank : (positiveCompositeSegmentVertexRank u v k c i z x hx).val <
        (positiveCompositeSegmentVertexRank u v k c j w y hy).val :=
      colorIntervalRanks_ordered _ _ _ _ _
        (positiveOccurrencePosition_strictMono u k hlt) _ _ hm1 hm2
    have hboundary := c.1.boundary_mono (by omega : 0 < (n + 1) + e)
      (show i.val + 1 ≤ j.val from hlt)
    rw [c.1.boundary_next (by omega : 0 < (n + 1) + e) i, c.1.boundary_at] at hboundary
    have hpos : c.1.start i + z.val ≤ c.1.start j + w.val := by
      have hz := z.isLt
      omega
    change (c.1.start i + z.val) +
        (positiveCompositeSegmentVertexRank u v k c i z x hx).val <
      (c.1.start j + w.val) + (positiveCompositeSegmentVertexRank u v k c j w y hy).val
    omega

/-- 元の全挿入色の頂点の写像は狭義順序を保つ（BF §2.2.6）。 -/
lemma insertedColorPathMap_strictMono {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    StrictMono (insertedColorPathMap u v k c b) := by
  intro x y hxy
  change (insertedColorPathMap u v k c b x).val < (insertedColorPathMap u v k c b y).val
  unfold insertedColorPathMap
  exact positiveCompositeSegmentInnerVertex_strict_order u v k c _ _ _ _ _ _ _ _ hxy

end SerrePositivity.EInfinity.SimplexCuts
