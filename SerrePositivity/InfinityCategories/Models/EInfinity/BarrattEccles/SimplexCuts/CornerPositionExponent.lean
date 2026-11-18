module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerIntervalMaxima
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
模型。文献の定義との比較は後で
# 混合角の交換によるBF位置指数の増分

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
右端が一つ進む区間だけを有限和から分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C138：角交換で直前の区間の右端は一つ進む。 -/
lemma hi_swapSteps_hv_at {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (s.swapSteps a b) (s.horizontal a.castSucc) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (s.horizontal a.castSucc) + 1 := by
  have hcoords := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapSteps_hv_coordinates s a b hab ha hb
  have hbm : b ∈ (s.swapSteps a b).val := by
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_right] using ha
  have hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (s.swapSteps a b) (s.horizontal a.castSucc) =
      ((s.swapSteps a b).vertical b.castSucc).val := by
    rw [← hcoords.1]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.interval_max_before_horizontal _ b hbm]
  have ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (s.horizontal a.castSucc) = (s.vertical b.castSucc).val := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.interval_max_before_horizontal s a ha]
    have hbc : b.castSucc = a.succ := Fin.ext hab
    rw [hbc, (s.step_of_mem a ha).2]
  rw [hn, ho]
  exact hcoords.2

/-- C139：混合角の位置指数は、その区間が元の語のcaesuraなら一だけ増える。 -/
lemma positionExponent_swapSteps_hv {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent (s.swapSteps a b) v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v +
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v (s.horizontal a.castSucc) then 1 else 0 := by
  let X := s.horizontal a.castSucc
  let F := fun i => if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i else 0
  have hf : (fun i => if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (s.swapSteps a b) i else 0) =
      Function.update F X (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v X then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s X + 1 else 0) := by
    funext i
    by_cases h : i = X
    · subst i
      rw [Function.update_self, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_swapSteps_hv_at s a b hab ha hb]
    · rw [Function.update_of_ne h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_swapSteps_hv_of_ne s a b hab ha hb i h]
  have h₁ := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ X) F
    (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v X then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s X + 1 else 0)
  have h₀ := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ X) F (F X)
  rw [Function.update_eq_self] at h₀
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent
  rw [hf]
  change _ = (∑ i, F i) + if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v X then 1 else 0
  by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v X
  · simp only [hc, ite_true, F] at h₁ h₀ ⊢
    omega
  · simp only [hc, ite_false, F] at h₁ h₀ ⊢
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
