module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerBoundaryTerms

/-!
模型。文献の定義との比較は後で
# 両向きの混合角での出力境界項の相殺

Berger–Fresse §2.2.7、M14 L09a。
垂直辺の両端で出力次数が正になることを使い、元の境界項の符号反転を得る。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C166：垂直辺の終点の出力次数は、その直前の同色の頂点により正。 -/
lemma outputDegree_pos_after_vertical {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin (m + q)) (ha : a ∉ s.val) :
    0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val a.succ) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_previous
  exact ⟨a.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.castSucc_lt_succ,
    congrArg v.val (s.step_of_notMem a ha).1.symm⟩⟩

/-- C167：混合角の両側の指定境界項は、向きによらず元の加群で相殺。 -/
lemma outputBoundaryTerm_swapSteps_mixed {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (hc : a ∈ s.val ↔ b ∉ s.val)
    (jo : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val b.castSucc) + 1))
    (jno : jo.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val b.castSucc) b.castSucc)
    (jn : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (s.swapSteps a b) v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank (s.swapSteps a b) v.val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S (s.swapSteps a b) v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v.val b.castSucc) jn x =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val b.castSucc) jo x := by
  have hbc : b.castSucc = a.succ := Fin.ext hab
  by_cases ha : a ∈ s.val
  · have hb := hc.mp ha
    have hna : a ∉ (s.swapSteps a b).val := by
      simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
    have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_active s v b.castSucc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.before_vertical_active s v.val b hb)
    have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_after_vertical (s.swapSteps a b) v a hna
    rw [← hbc] at hn
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_swapSteps_of_sign A S s v a b hab ho hn jo jno jn jnn
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_swapSteps_hv s v a b hab ha hb) x
  · have hb : b ∈ s.val := by by_contra h; exact ha (hc.mpr h)
    have hnb : b ∉ (s.swapSteps a b).val := by
      simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_right] using ha
    have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_after_vertical s v a ha
    rw [← hbc] at ho
    have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_active (s.swapSteps a b) v b.castSucc
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.before_vertical_active (s.swapSteps a b) v.val b hnb)
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_swapSteps_of_sign A S s v a b hab ho hn jo jno jn jnn
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_swapSteps_vh s v a b hab ha hb) x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
