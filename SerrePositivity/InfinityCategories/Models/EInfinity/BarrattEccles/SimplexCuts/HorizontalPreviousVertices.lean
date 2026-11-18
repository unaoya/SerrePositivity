module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PreviousVertexPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 一頂点の水平区間の直前の同色頂点

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
元の語の直前同色区間の最後を、展開語の直前同色頂点として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C178：一頂点の水平区間の直前同色頂点は、直前同色区間の最後。 -/
lemma previousVertex_label_horizontal_singleton {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a).Nonempty)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k he =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp)).max'
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp
  let j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s p)
  have hj : s.horizontal j = p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s p
  have hpa : p < a := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_lt v a hp
  have hjk : j < k := by
    by_contra hn
    have hmono := s.horizontal.monotone (le_of_not_gt hn)
    rw [hj, hk] at hmono
    exact (not_le_of_gt hpa) hmono
  have hmem : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk, ?_⟩
    change v (s.horizontal j) = v (s.horizontal k)
    rw [hj, hk]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_value v a hp
  apply (Finset.max'_eq_iff _ _ _).mpr
  refine ⟨hmem, ?_⟩
  intro l hl
  have hlk := (Finset.mem_filter.mp hl).2.1
  have hcolor := (Finset.mem_filter.mp hl).2.2
  have hla : s.horizontal l < a := by
    have hle := s.horizontal.monotone hlk.le
    rw [hk] at hle
    apply lt_of_le_of_ne hle
    intro heq
    exact (ne_of_lt hlk) (hsingle l heq)
  have hprev : s.horizontal l ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla, ?_⟩
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label, hk] using hcolor
  have hle : s.horizontal l ≤ p := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a).le_max' _ hprev
  by_contra hn
  have hjl : j < l := lt_of_not_ge hn
  have hge := s.horizontal.monotone hjl.le
  rw [hj] at hge
  have heq := le_antisymm hle hge
  exact (not_le_of_gt hjl) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p).le_max' l
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
