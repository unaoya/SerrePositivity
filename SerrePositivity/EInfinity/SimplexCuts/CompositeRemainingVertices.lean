module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeRemainingPositions
public import SerrePositivity.EInfinity.SimplexCuts.IntervalVertexCoordinates

/-!
# 同じ合成語に残る外側の元の頂点

Berger–Fresse §2.2.6、M14 L12a の指定面の照合。
残り色の一文字の区間は、元の外側区間と同じ高さの頂点を持つ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C451g：残り色の元の頂点は、同じ合成位置で同じ二座標を持つ（BF §2.2.6）。 -/
lemma positiveCompositeRemainingVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) (h : Fin (q + 1))
    (hl : lo (positiveCompositeOuterCut u v k c) p ≤ h.val)
    (hr : h.val ≤ hi (positiveCompositeOuterCut u v k c) p) :
    c.2.horizontal (coordinatePosition (compositeFirstPosition u v k c.1 p) h) =
        compositeFirstPosition u v k c.1 p ∧
      c.2.vertical (coordinatePosition (compositeFirstPosition u v k c.1 p) h) = h := by
  apply coordinates_of_interval
  · rw [← (positiveCompositeOuterCut_endpoints u v k c p).1]
    exact hl
  · rw [compositeFirstPosition_eq_last_of_non_slot u v k c.1 p hp,
      ← (positiveCompositeOuterCut_endpoints u v k c p).2]
    exact hr

end SerrePositivity.EInfinity.SimplexCuts
