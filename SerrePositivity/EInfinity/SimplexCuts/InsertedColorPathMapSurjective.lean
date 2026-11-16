module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorPathMapEvaluation
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInverseVertices
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceComparison

/-!
# 元の挿入色の全頂点の写像の全射性

Berger–Fresse §2.2.6、M14 L12a のC451。
内側の二座標を同じ外側順位の元の部分語へ戻し、同じ合成頂点を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の挿入色の全頂点は、同じ内側Cutの全ての同色頂点を覆う（BF §2.2.6）。 -/
lemma insertedColorPathMap_surjective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    Function.Surjective (insertedColorPathMap u v k c b) := by
  intro y
  let a := (positiveCompositeInnerCut u v k c).horizontal y.val
  let rank := (positiveCompositeInnerCut u v k c).vertical y.val
  obtain ⟨p, hp, hmem⟩ := colorIntervalRanks_cover (positiveCompositeOuterCut u v k c)
    (positiveWord u) k rank
  obtain ⟨j, hj⟩ := occurrenceAt_exists (positiveWord u).val k p hp
  let i : Fin (Surjection.occurrenceCount u.val k) := Fin.cast (positiveWord_occurrenceCount u k) j
  have hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) := by
    rw [positiveOccurrencePosition_eq u k i j rfl, hj]
    exact hmem
  have hl := lo_le_vertical (positiveCompositeInnerCut u v k c) a y.val rfl
  have hr := vertical_le_hi (positiveCompositeInnerCut u v k c) a y.val rfl
  have hcover := positiveCompositeInnerPosition_segment_covered u v k c i a rank hm hl hr
  let z : Fin (c.1.val i).val := ⟨a.val - c.1.start i, by omega⟩
  have hja : positiveCompositeSegmentInnerPosition u v k c i z = a := by
    apply Fin.ext
    change c.1.start i + (a.val - c.1.start i) = a.val
    omega
  have hlo : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val := by rw [hja]; exact hl
  have hhi : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) := by rw [hja]; exact hr
  let inv := positiveCompositeSegmentInverseVertex u v k c i z rank
  have hc := positiveCompositeSegmentInverseVertex_coordinates u v k c i z rank hm hlo hhi
  have hrank := positiveCompositeSegmentInverseVertex_rank u v k c i z rank hm hlo hhi
  have hmap : positiveCompositeSegmentInnerVertex u v k c i z inv hc.1 = y.val := by
    have hcoord := positiveCompositeSegmentInnerVertex_coordinates u v k c i z inv hc.1
    apply (positiveCompositeInnerCut u v k c).vertex_injective
    apply Prod.ext
    · exact hcoord.1.trans hja
    · exact hcoord.2.trans hrank
  have hlabel := positiveCompositeSegmentInnerVertex_label u v k c i z inv hc.1
  rw [hmap] at hlabel
  have hyLabel : label (positiveCompositeInnerCut u v k c) (positiveWord v).val y.val = b :=
    (Finset.mem_filter.mp y.property).2
  have hsource : inv ∈ colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hlabel.trans (congrArg (BarrattEccles.insertedPosition m (n + 1) k) hyLabel)⟩
  let x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)) := ⟨inv, hsource⟩
  refine ⟨x, Subtype.ext ?_⟩
  exact (insertedColorPathMap_val_of_segment u v k c b x i z hc.1).trans hmap

end SerrePositivity.EInfinity.SimplexCuts
