module
public import SerrePositivity.InfinityCategories.Derived.DGSourceRefinementLinear

/-! # 始点細分に伴う順方向 Hom 写像の合成整合性

概要：増加する三頂点の Hom の写像は、全次数の通常順合成を厳密に保つ。
方針：零始点では閉前合成の結合則、正始点では対象輸送の合成則を使う。
規約：単位や逆方向 Hom には主張しない。使われ方：任意次数の単体 rhs の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉前合成は、その後の任意次数の合成と厳密に可換。 -/
lemma dgGradedPrecompose_compose {w x y z : D} {p r k : ℤ}
    (g : GradedHom A y z r) (f : GradedHom A x y p) (h : p + r = k)
    (s : ForgetEnrichment.of (Complex A) w ⟶ ForgetEnrichment.of (Complex A) x) :
    dgGradedPrecompose A D k (compose A g f h) s =
      compose A g (dgGradedPrecompose A D p f s) h := by
  exact (compose_assoc_of_sum (closedHomEquiv A D _ _ s).val f g (zero_add p) h h).symm

variable {n : ℕ} (o : Fin (n + 1) → D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (o 0))

/-- 順方向の三つの Hom の写像は、全整数次数の合成を厳密に保つ。 -/
lemma dgSourceRefinementHomLinear_compose (a j b : Fin (n + 1)) (haj : a < j) (hjb : j < b)
    {p r k : ℤ} (g : GradedHom A (o j) (o b) r) (f : GradedHom A (o a) (o j) p)
    (h : p + r = k) :
    dgSourceRefinementHomLinear A D o q s a b k (compose A g f h) =
      compose A (dgSourceRefinementHomLinear A D o q s j b r g)
        (dgSourceRefinementHomLinear A D o q s a j p f) h := by
  have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) haj)
  have hb : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le j) hjb)
  by_cases ha : a = 0
  · subst a
    rw [dgSourceRefinementHomLinear_from_zero A D o q s b hb,
      dgSourceRefinementHomLinear_of_ne_zero A D o q s j b hj hb,
      dgSourceRefinementHomLinear_from_zero A D o q s j hj]
    exact (congrArg (gradedHomTransport (A := A) (rfl : q = q)
      (dgSourceRefinementObj_ne_zero D o q b hb).symm (rfl : k = k))
        (dgGradedPrecompose_compose A D g f h s)).trans
          (gradedHomTransport_compose rfl (dgSourceRefinementObj_ne_zero D o q j hj).symm
            (dgSourceRefinementObj_ne_zero D o q b hb).symm rfl rfl rfl
              g (dgGradedPrecompose A D p f s) h)
  · rw [dgSourceRefinementHomLinear_of_ne_zero A D o q s a b ha hb,
      dgSourceRefinementHomLinear_of_ne_zero A D o q s j b hj hb,
      dgSourceRefinementHomLinear_of_ne_zero A D o q s a j ha hj]
    exact gradedHomTransport_compose (dgSourceRefinementObj_ne_zero D o q a ha).symm
      (dgSourceRefinementObj_ne_zero D o q j hj).symm
      (dgSourceRefinementObj_ne_zero D o q b hb).symm rfl rfl rfl g f h

end SerrePositivity.InfinityCategories
