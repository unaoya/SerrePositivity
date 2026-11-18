module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InsertedColorPathMapSurjective

/-!
模型。文献の定義との比較は後で
# 元の挿入頂点の順序は同じ内側経路で保たれる

Berger–Fresse §2.2.6、M14 L12a のC451。
同じ部分語では座標和の平行移動、異なる部分語では元の境界と色別順位を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の合成経路の順序は、指定した同じ内側頂点の順序を保つ（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_strict_order {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 j w) (hxy : x < y) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex u v k c i z x hx <
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex u v k c j w y hy := by
  have hij : i ≤ j := by
    by_contra hn
    have hlt : j < i := lt_of_not_ge hn
    have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 j w).val <
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z).val :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition_lt u v k c.1 j i hlt w z
    have hs := c.2.horizontal.monotone hxy.le
    rw [hx, hy] at hs
    have hval : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z).val ≤
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 j w).val := hs
    omega
  rcases eq_or_lt_of_le hij with he | hlt
  · subst j
    have hsx := c.2.coordinate_sum x
    have hsy := c.2.coordinate_sum y
    rw [hx] at hsx
    rw [hy] at hsy
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val +
      z.val + (c.2.vertical x).val = x.val at hsx
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val +
      w.val + (c.2.vertical y).val = y.val at hsy
    have hbx := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegment_outer_bounds u v k c i z x hx).1
    have hby := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegment_outer_bounds u v k c i w y hy).1
    let first := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i)).val
    change (c.1.start i + z.val) +
        (first + ((c.2.vertical x).val -
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i))) <
      (c.1.start i + w.val) +
        (first + ((c.2.vertical y).val -
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i)))
    have hval : x.val < y.val := hxy
    omega
  · have hm1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank_mem u v k c i z x hx
    have hm2 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank_mem u v k c j w y hy
    have hrank : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank u v k c i z x hx).val <
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank u v k c j w y hy).val :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalRanks_ordered _ _ _ _ _
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_strictMono u k hlt) _ _ hm1 hm2
    have hboundary := c.1.boundary_mono (by omega : 0 < (n + 1) + e)
      (show i.val + 1 ≤ j.val from hlt)
    rw [c.1.boundary_next (by omega : 0 < (n + 1) + e) i, c.1.boundary_at] at hboundary
    have hpos : c.1.start i + z.val ≤ c.1.start j + w.val := by
      have hz := z.isLt
      omega
    change (c.1.start i + z.val) +
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank u v k c i z x hx).val <
      (c.1.start j + w.val) + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentVertexRank u v k c j w y hy).val
    omega

/-- 元の全挿入色の頂点の写像は狭義順序を保つ（BF §2.2.6）。 -/
lemma insertedColorPathMap_strictMono {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap u v k c b) := by
  intro x y hxy
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap u v k c b x).val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap u v k c b y).val
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex_strict_order u v k c _ _ _ _ _ _ _ _ hxy

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
