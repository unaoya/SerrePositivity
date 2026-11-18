module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorHeightVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NestedPartitionHeightInterval

/-!
模型。文献の定義との比較は後で
# 同じ区間内の元の頂点と順位の相互復元

Berger–Fresse §2.2.6、M14 L12a の逆の等式の証明分割。
同じ区間内では高さの差と順位の差が一致し、元の順位へ厳密に戻る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C436：同じ区間の頂点の高さから元の順位へ戻る（BF §2.2.6）。 -/
lemma colorHeightRank_vertices {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalRanks s v a p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorHeightRank s v a p hp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s v a j).val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_bounds_on_colorInterval s v a p j hj).1
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_bounds_on_colorInterval s v a p j hj).2 = j := by
  apply Fin.ext
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_on_colorIntervalRanks s v a p hp j hj
  have hfirst : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst s v a p hp).val ≤ j.val :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalRanks s v a p).min'_le j hj
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst s v a p hp).val + ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s v a j).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p) = j.val
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
