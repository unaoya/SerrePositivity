module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedConjugation
/-!
概要：斉次閉射の単位関係を使い、次数零の比較から元の次数の境界原始元を回収する。
方針：同じ Leibniz 微分と符号付き前後合成を使う。
規約：cochain を変更しない。使われ方：H⁰ の充満忠実性による全 Hom の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedBoundary_precompose_closed {x y z : D} {p q k l r : ℤ}
    (hpq : p + q = k) (hkl : k + 1 = l) (hdr : q + 1 = r)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0)
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D x z).d k l (_root_.SerrePositivity.DifferentialGraded.compose R b f hpq) =
      _root_.SerrePositivity.DifferentialGraded.compose R ((_root_.SerrePositivity.DifferentialGraded.homObject R D y z).d q r b) f (by omega) := by
  subst r l
  change _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.DifferentialGraded.compose R b f hpq) = _
  rw [differential_compose, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedClosed_postcompose_boundary {x y z : D} {p q k l : ℤ}
    (hpq : p + q = k) (hkl : k + 1 = l)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D x z).d k l (q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R a b hpq) =
      _root_.SerrePositivity.DifferentialGraded.compose R a (_root_.SerrePositivity.DifferentialGraded.differential R b) (by omega) := by
  subst l
  change _root_.SerrePositivity.DifferentialGraded.differential R (q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R a b hpq) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, differential_compose, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add,
    smul_smul, Int.units_mul_self, one_smul]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedCycle_lift_recover {x w z : D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w n) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x (-n))
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R D x x).d (-1) 0 h =
      _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom R w z 0) (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R w z (-1))
    (hb : (_root_.SerrePositivity.DifferentialGraded.homObject R D w z).d (-1) 0 b = _root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n) - c) :
    ∃ t : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z (n - 1), (_root_.SerrePositivity.DifferentialGraded.homObject R D x z).d (n - 1) n t =
      a - _root_.SerrePositivity.DifferentialGraded.compose R c f (add_zero n) := by
  refine ⟨_root_.SerrePositivity.DifferentialGraded.compose R b f (by omega) - n.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R a h (by omega), ?_⟩
  rw [map_sub, dgGradedBoundary_precompose_closed R D (r := 0) _ (by omega) (by decide) f hf,
    dgGradedClosed_postcompose_boundary R D _ (by omega) a ha]
  change _root_.SerrePositivity.DifferentialGraded.differential R h = _ at hh
  rw [hb, hh, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, compose_unit]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D f g a (add_neg_cancel n) (neg_add_cancel n)
    (zero_add n) (add_zero n)]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
