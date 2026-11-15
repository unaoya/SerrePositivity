module

public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightVertices

/-!
# 元の一つの色別区間での頂点の順序

Berger–Fresse §2.2.6、M14 L12a の指定頂点の比較の法則。
区間内の元の高さの差で、同じ順位の大小を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ外側区間の上では、元のverticesは順序を反映する（BF §2.2.6）。 -/
lemma vertices_le_iff_on_colorInterval {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (i j : Fin (outputDegree s v a + 1))
    (hi : i ∈ colorIntervalRanks s v a p) (hj : j ∈ colorIntervalRanks s v a p) :
    vertices s v a i ≤ vertices s v a j ↔ i ≤ j := by
  constructor
  · intro h
    have hv : (vertices s v a i).val ≤ (vertices s v a j).val := h
    rw [vertices_on_colorIntervalRanks s v a p hp i hi,
      vertices_on_colorIntervalRanks s v a p hp j hj] at hv
    have hfi : (colorIntervalFirst s v a p hp).val ≤ i.val :=
      (colorIntervalRanks s v a p).min'_le i hi
    have hfj : (colorIntervalFirst s v a p hp).val ≤ j.val :=
      (colorIntervalRanks s v a p).min'_le j hj
    change i.val ≤ j.val
    omega
  · intro h
    exact (vertices s v a).monotone h

end SerrePositivity.EInfinity.SimplexCuts
