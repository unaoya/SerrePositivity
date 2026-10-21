module
public import SerrePositivity.InfinityCategories.Derived.DGGradedConjugation
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedBoundary_precompose_closed {x y z : D} {p q k l r : ℤ}
    (hpq : p + q = k) (hkl : k + 1 = l) (hdr : q + 1 = r)
    (f : GradedHom R x y p) (hf : differential R f = 0)
    (b : GradedHom R y z q) :
    (homObject R D x z).d k l (compose R b f hpq) =
      compose R ((homObject R D y z).d q r b) f (by omega) := by
  subst r l
  change differential R (compose R b f hpq) = _
  rw [differential_compose, hf, compose_zero, smul_zero, add_zero]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedClosed_postcompose_boundary {x y z : D} {p q k l : ℤ}
    (hpq : p + q = k) (hkl : k + 1 = l)
    (a : GradedHom R y z q) (ha : differential R a = 0)
    (b : GradedHom R x y p) :
    (homObject R D x z).d k l (q.negOnePow • compose R a b hpq) =
      compose R a (differential R b) (by omega) := by
  subst l
  change differential R (q.negOnePow • compose R a b hpq) = _
  rw [differential_units_smul, differential_compose, ha, zero_compose, zero_add,
    smul_smul, Int.units_mul_self, one_smul]
/-- 元の斉次合成と同じ符号による境界の回収。 -/
lemma dgGradedCycle_lift_recover {x w z : D} (n : ℤ)
    (f : GradedHom R x w n) (g : GradedHom R w x (-n))
    (hf : differential R f = 0)
    (h : GradedHom R x x (-1))
    (hh : (homObject R D x x).d (-1) 0 h =
      compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (a : GradedHom R x z n) (ha : differential R a = 0)
    (c : GradedHom R w z 0) (b : GradedHom R w z (-1))
    (hb : (homObject R D w z).d (-1) 0 b = compose R a g (neg_add_cancel n) - c) :
    ∃ t : GradedHom R x z (n - 1), (homObject R D x z).d (n - 1) n t =
      a - compose R c f (add_zero n) := by
  refine ⟨compose R b f (by omega) - n.negOnePow • compose R a h (by omega), ?_⟩
  rw [map_sub, dgGradedBoundary_precompose_closed R D (r := 0) _ (by omega) (by decide) f hf,
    dgGradedClosed_postcompose_boundary R D _ (by omega) a ha]
  change differential R h = _ at hh
  rw [hb, hh, compose_sub_left, compose_sub_right, compose_unit]
  rw [dgNerveGradedCompose_assoc R D f g a (add_neg_cancel n) (neg_add_cancel n)
    (zero_add n) (add_zero n)]
  abel
end SerrePositivity.InfinityCategories
