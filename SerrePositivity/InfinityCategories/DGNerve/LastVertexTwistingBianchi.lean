module
public import SerrePositivity.InfinityCategories.DGNerve.HornResidual

/-!
概要：最後の頂点への残差が共通の次数一作用であるときの Bianchi 恒等式。
方針：削除・右切断の残差から作用を外へ出し、左切断の方程式で残りを除く。
規約：既存の単体データと通常順の斉次合成を使用する。
使われ方：coherent bar の列における二次項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma residualContribution_last_twisting {n : ℕ} (s : SimplexData A D n)
    (b : Fin (n + 1)) (θ : GradedHom A (s.obj b) (s.obj b) 1)
    (hEnd : ∀ (J : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
      (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
      (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      s.residual J a b k hJ ha hb hk =
        -compose A θ (s.hom J a b k hJ ha hb hk) rfl)
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hL : s.Equation (I.filter (· ≤ j))) :
    s.residualContribution I a b k hI ha hb hk j hj haj hjb =
      -compose A θ (s.term I a b k hI ha hb hk j hj haj hjb) rfl := by
  simp only [residualContribution, hEnd, residual_zero_of_equation s _ hL,
    compose_zero, smul_zero, sub_zero, term, Index.sign]
  have hneg {x y z : D} {p q r : ℤ} (g : GradedHom A y z q)
      (f : GradedHom A x y p) (h : p + q = r) :
      compose A (-g) f h = -compose A g f h := by
    simpa only [zero_sub, zero_compose] using compose_sub_left (0 : GradedHom A y z q) g f h
  rw [hneg, ← compose_assoc_of_sum _ _ θ
    (by have := Index.split_card hj; omega) rfl rfl]
  simp only [compose_units_smul_right, compose_sub_right, smul_sub,
    sub_neg_eq_add, neg_sub, smul_add, smul_neg]
  abel


lemma differential_rhs_last_twisting {n : ℕ} (s : SimplexData A D n)
    (b : Fin (n + 1)) (θ : GradedHom A (s.obj b) (s.obj b) 1)
    (hOld : ∀ J : Finset (Fin (n + 1)), b ∉ J → s.Equation J)
    (hEnd : ∀ (J : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
      (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
      (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      s.residual J a b k hJ ha hb hk =
        -compose A θ (s.hom J a b k hJ ha hb hk) rfl)
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) =
      -compose A θ (s.rhs I a b k hI ha hb hk) rfl := by
  rw [bianchi]
  unfold rhs
  rw [compose_sum_right, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · exact residualContribution_last_twisting s b θ hEnd I a k hI ha hb hk
      j.val j.property h.1 h.2 (hOld _ (by
        intro hbL
        exact (not_le_of_gt h.2) (Finset.mem_filter.mp hbL).2))
  · simp only [compose_zero, neg_zero]


lemma curvature_comp_last_twisting {n : ℕ} (s : SimplexData A D n)
    (b : Fin (n + 1)) (θ : GradedHom A (s.obj b) (s.obj b) 1)
    (hOld : ∀ J : Finset (Fin (n + 1)), b ∉ J → s.Equation J)
    (hEnd : ∀ (J : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
      (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
      (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      s.residual J a b k hJ ha hb hk =
        -compose A θ (s.hom J a b k hJ ha hb hk) rfl)
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hclosed : differential A (s.hom I a b k hI ha hb hk) = 0)
    (hrhs : s.rhs I a b k hI ha hb hk =
      compose A θ (s.hom I a b k hI ha hb hk) rfl) :
    compose A (differential A θ + compose A θ θ rfl)
      (s.hom I a b k hI ha hb hk) (show k + 2 = k + 1 + 1 by omega) = 0 := by
  have hd := differential_rhs_last_twisting s b θ hOld hEnd I a k hI ha hb hk
  rw [hrhs, differential_compose, hclosed, compose_zero, smul_zero, add_zero] at hd
  rw [compose_add_left]
  apply add_eq_zero_iff_eq_neg.mpr
  exact hd.trans (congrArg Neg.neg
    (compose_assoc_of_sum _ _ _ rfl rfl rfl))

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
