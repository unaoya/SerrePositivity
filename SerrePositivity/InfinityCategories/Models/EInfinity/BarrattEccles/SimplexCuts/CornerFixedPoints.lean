module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerInvolution

/-!
模型。文献の定義との比較は後で
# 角交換の固定点と混合角

Berger–Fresse §2.2.7、M14 L09a。
同じ向きの辺の交換は固定点であり、異なる向きの辺の交換だけが非固定点になる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C41：二辺の交換が切断を変えないのは、両辺の向きが同じとき。 -/
lemma swapSteps_eq_self_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (a b : Fin (m + q)) :
    s.swapSteps a b = s ↔ (a ∈ s.val ↔ b ∈ s.val) := by
  constructor
  · intro h
    have he := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q => a ∈ t.val) h
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using
      (Iff.of_eq he).symm
  · intro h
    apply Subtype.ext
    ext x
    simp only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps]
    by_cases ha : x = a
    · subst x
      simpa only [Equiv.swap_apply_left] using h.symm
    · by_cases hb : x = b
      · subst x
        simpa only [Equiv.swap_apply_right] using h
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- 指定頂点が内部の混合角であること。 -/
def MixedVertex {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) : Prop :=
  ∃ h : 0 < k.val ∧ k.val < m + q,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge k h ∈ s.val ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∉ s.val

/-- C42：角交換の非固定点は内部の混合角とちょうど一致する。 -/
lemma swapAtVertex_ne_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex s k ≠ s ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex s k := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex
  by_cases h : 0 < k.val ∧ k.val < m + q
  · rw [dite_eq_left h, ne_eq, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapSteps_eq_self_iff]
    constructor
    · intro hn
      refine ⟨h, ?_⟩
      tauto
    · rintro ⟨_, hc⟩
      tauto
  · rw [dite_eq_right h]
    simp only [ne_self_iff_false, false_iff]
    rintro ⟨h', _⟩
    exact h h'

/-- C43：混合角は交換後も混合角。 -/
lemma mixedVertex_swapAtVertex_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex s k) k ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex s k := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex_ne_iff, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex_ne_iff]
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex s k) k = s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex_involutive k s
  rw [hs]
  exact ne_comm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
