module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerRanks
public import SerrePositivity.EInfinity.SimplexCuts.IntervalVertexCoordinates

/-!
# 元の挿入頂点を同じ内側切断の二座標で読む

Berger–Fresse §2.2.6、M14 L12a の指定頂点の照合。
同じ内側位置と外側順位を元のcoordinatePositionに渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の挿入頂点に対応する同じ内側の経路位置（BF §2.2.6）。 -/
def positiveCompositeSegmentInnerVertex {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    Fin (n + e + outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1) :=
  coordinatePosition (positiveCompositeSegmentInnerPosition u v k c i z)
    (positiveCompositeSegmentVertexRank u v k c i z x hx)

/-- 指定した二座標は元の同じ内側Cutで実現される（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    (positiveCompositeInnerCut u v k c).horizontal
        (positiveCompositeSegmentInnerVertex u v k c i z x hx) =
        positiveCompositeSegmentInnerPosition u v k c i z ∧
      (positiveCompositeInnerCut u v k c).vertical
        (positiveCompositeSegmentInnerVertex u v k c i z x hx) =
        positiveCompositeSegmentVertexRank u v k c i z x hx :=
  coordinates_of_interval _ _ _ (positiveCompositeSegmentRank_inner_bounds u v k c i z x hx).1
    (positiveCompositeSegmentRank_inner_bounds u v k c i z x hx).2

/-- 元の二段の指定面で読むと、同じ合成頂点の高さとなる（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical
        (positiveCompositeSegmentInnerVertex u v k c i z x hx)) = c.2.vertical x := by
  rw [(positiveCompositeSegmentInnerVertex_coordinates u v k c i z x hx).2]
  exact positiveCompositeSegmentVertexRank_vertices u v k c i z x hx

/-- 同じ内側頂点の文字は、元の挿入ラベルと一致（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_label {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    label c.2 (positiveCompositeCutWord u v k c.1).val x =
      BarrattEccles.insertedPosition m (n + 1) k
        (label (positiveCompositeInnerCut u v k c) (positiveWord v).val
          (positiveCompositeSegmentInnerVertex u v k c i z x hx)) := by
  unfold label
  rw [hx, positiveCompositeSegmentPosition_label,
    (positiveCompositeSegmentInnerVertex_coordinates u v k c i z x hx).1]
  congr 1
  unfold positiveWord
  exact (word_eq_mp_value (by omega : (n + 1) + e = n + e + 1) v
    (positiveCompositeSegmentInnerPosition u v k c i z)
    ⟨c.1.start i + z.val, by
      have h := c.1.start_add_length_le i; have hz := z.isLt; omega⟩ rfl).symm

end SerrePositivity.EInfinity.SimplexCuts
