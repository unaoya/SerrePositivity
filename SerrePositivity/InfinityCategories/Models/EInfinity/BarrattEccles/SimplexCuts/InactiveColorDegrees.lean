module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PreviousBoundarySigns

/-!
模型。文献の定義との比較は後で
# 非活動で直前同色を持たない出力の次数

Berger–Fresse §2.2.7、M14 L09a。
前後に同色がない頂点は、その色の唯一の頂点であり、出力の次数は零となる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C118：前後に同色を持たない経路頂点の色のfiberは一頂点。 -/
lemma colorPositions_singleton_of_inactive_no_previous {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1))
    (hk : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v)
    (hp : ¬(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v k) = {k} := by
  ext j
  constructor
  · intro hj
    apply Finset.mem_singleton.mpr
    have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v k := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy j k with hlt | he | hgt
    · exact False.elim (hp ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hc⟩⟩)
    · exact he
    · exact False.elim (hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hgt, hc⟩))
  · intro hj
    exact Finset.mem_singleton.mp hj ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- C119：前後に同色がない頂点の色の出力次数は零。 -/
lemma outputDegree_zero_of_inactive_no_previous {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val)
    (hp : ¬(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_singleton_of_inactive_no_previous s v.val k hk hp, Finset.card_singleton]

/-- C120：正の出力次数を持つ非活動頂点には、直前同色の活動頂点が存在する。 -/
lemma previousOccurrences_nonempty_of_inactive_degree_pos {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val) (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty := by
  by_contra hp
  have hz := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_of_inactive_no_previous s v k hk hp
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
