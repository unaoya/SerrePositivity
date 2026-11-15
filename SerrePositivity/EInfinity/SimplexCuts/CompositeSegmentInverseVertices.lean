module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInverseInterval

/-!
# 元の内側順位から同じ合成頂点を復元する

Berger–Fresse §2.2.6、M14 L12a のC451の逆方向。
同じ部分語位置と元の外側verticesの高さを、元の経路の二座標として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の部分語位置と外側の指定高さによる同じ合成位置（BF §2.2.6）。 -/
def positiveCompositeSegmentInverseVertex {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1)) :
    Fin (m + n + (d + e) + q + 1) :=
  coordinatePosition (positiveCompositeSegmentPosition u v k c.1 i z)
    (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank)

/-- 同じ内側区間に属する順位は、元の合成経路で二座標を実現する（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInverseVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    c.2.horizontal (positiveCompositeSegmentInverseVertex u v k c i z rank) =
        positiveCompositeSegmentPosition u v k c.1 i z ∧
      c.2.vertical (positiveCompositeSegmentInverseVertex u v k c i z rank) =
        vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank :=
  coordinates_of_interval _ _ _
    (positiveCompositeSegment_inverse_interval u v k c i z rank hm hl hr).1
    (positiveCompositeSegment_inverse_interval u v k c i z rank hm hl hr).2

/-- 同じ逆頂点の高さから、元の外側色別順位へ戻る（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInverseVertex_rank {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    positiveCompositeSegmentVertexRank u v k c i z
        (positiveCompositeSegmentInverseVertex u v k c i z rank)
        (positiveCompositeSegmentInverseVertex_coordinates u v k c i z rank hm hl hr).1 = rank := by
  apply Fin.ext
  have hv := congrArg Fin.val
    (positiveCompositeSegmentInverseVertex_coordinates u v k c i z rank hm hl hr).2
  have hf : (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)).val ≤ rank.val :=
    (colorIntervalRanks _ _ _ _).min'_le rank hm
  have hformula := vertices_on_colorIntervalRanks (positiveCompositeOuterCut u v k c)
    (positiveWord u) k (positiveOccurrencePosition u k i)
    (positiveOccurrencePosition_value u k i) rank hm
  change (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)).val +
    ((c.2.vertical (positiveCompositeSegmentInverseVertex u v k c i z rank)).val -
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i)) = rank.val
  rw [hv, hformula]
  omega

end SerrePositivity.EInfinity.SimplexCuts
