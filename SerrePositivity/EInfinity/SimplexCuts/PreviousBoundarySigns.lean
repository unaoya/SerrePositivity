module

public import SerrePositivity.EInfinity.SimplexCuts.PreviousVertexPositions

/-!
# 同色の直前の面に移したBF境界符号

Berger–Fresse §2.2.7、M14 L09a。
同じ色の連続する面番号の差一を使い、最後の非活動頂点も活動頂点の式へ運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (positionInversionCount)

lemma outputBoundarySignAt_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
      ((∑ c ∈ Finset.univ.filter (fun c : Fin r => c < label s v.val k), outputDegree s v c) +
      vertexRank s v.val (label s v.val k) k) := by
  unfold outputBoundarySignAt outputBoundarySign
  rw [← vertexRank_symm_colorPositionEquiv s v k, colorPositionEquiv_symm_color]

/-- C116：同色の直前の頂点の境界符号とは、面番号が一つ違うので反対。 -/
lemma outputBoundarySignAt_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
    outputBoundarySignAt s v k =
      -outputBoundarySignAt s v (previousVertex (label s v.val) k h) := by
  have hc := previousVertex_value (label s v.val) k h
  have hr := vertexRank_previousVertex s v.val k h
  rw [hc] at hr
  rw [outputBoundarySignAt_rank, outputBoundarySignAt_rank, hc, hr]
  simp only [← Nat.add_assoc, pow_succ, mul_neg, mul_one]

/-- C117：直前の活動頂点の逆転集合で、指定頂点のBF境界符号を計算する。 -/
lemma outputBoundarySignAt_via_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
    outputBoundarySignAt s v k = -
      ((-1 : ℤ) ^ positionExponent s v.val *
        (-1 : ℤ) ^ positionInversionCount (label s v.val)
          ((activeVertexPositions s v.val).erase (previousVertex (label s v.val) k h)) *
        (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter
          (fun j => j < previousVertex (label s v.val) k h)).card) := by
  rw [outputBoundarySignAt_previous s v k h,
    outputBoundarySignAt_of_active s v _ (previousVertex_active s v.val k h)]

end SerrePositivity.EInfinity.SimplexCuts
