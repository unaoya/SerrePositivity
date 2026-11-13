module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSourceRefinementLinear

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉前合成は、その後の任意次数の合成と厳密に可換。 -/
lemma dgGradedPrecompose_compose {w x y z : D} {p r k : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A y z r) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y p) (h : p + r = k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (compose A g f h) s =
      compose A g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D p f s) h := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (closedHomEquiv A D _ _ s).val f g (zero_add p) h h).symm

variable {n : ℕ} (o : Fin (n + 1) → D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (o 0))

/-- 順方向の三つの Hom の写像は、全整数次数の合成を厳密に保つ。 -/
lemma dgSourceRefinementHomLinear_compose (a j b : Fin (n + 1)) (haj : a < j) (hjb : j < b)
    {p r k : ℤ} (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o j) (o b) r) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o a) (o j) p)
    (h : p + r = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s a b k (compose A g f h) =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s j b r g)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s a j p f) h := by
  have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) haj)
  have hb : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le j) hjb)
  by_cases ha : a = 0
  · subst a
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_from_zero A D o q s b hb,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D o q s j b hj hb,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_from_zero A D o q s j hj]
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (rfl : q = q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q b hb).symm (rfl : k = k))
        (dgGradedPrecompose_compose A D g f h s)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q j hj).symm
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q b hb).symm rfl rfl rfl
              g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D p f s) h)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D o q s a b ha hb,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D o q s j b hj hb,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D o q s a j ha hj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q a ha).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q j hj).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D o q b hb).symm rfl rfl rfl g f h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
