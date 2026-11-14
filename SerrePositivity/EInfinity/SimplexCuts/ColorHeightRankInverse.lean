module

public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightVertices
public import SerrePositivity.EInfinity.SimplexCuts.NestedPartitionHeightInterval

/-!
# 同じ区間内の元の頂点と順位の相互復元

Berger–Fresse §2.2.6、M14 L12a の逆の等式の証明分割。
同じ区間内では高さの差と順位の差が一致し、元の順位へ厳密に戻る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C436：同じ区間の頂点の高さから元の順位へ戻る（BF §2.2.6）。 -/
lemma colorHeightRank_vertices {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    colorHeightRank s v a p hp (vertices s v a j).val
        (vertices_bounds_on_colorInterval s v a p j hj).1
        (vertices_bounds_on_colorInterval s v a p j hj).2 = j := by
  apply Fin.ext
  have hv := vertices_on_colorIntervalRanks s v a p hp j hj
  have hfirst : (colorIntervalFirst s v a p hp).val ≤ j.val :=
    (colorIntervalRanks s v a p).min'_le j hj
  change (colorIntervalFirst s v a p hp).val + ((vertices s v a j).val - lo s p) = j.val
  omega

end SerrePositivity.EInfinity.SimplexCuts
