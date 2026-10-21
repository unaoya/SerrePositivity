module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroCycleLifting
public import SerrePositivity.InfinityCategories.Derived.DGGradedCycleRecovery
/-!
概要：H⁰ の充満忠実性と実斉次 shift から全次数の閉 cochain を比較する。
方針：次数零の持ち上げ・反映の後、同じ単位差の原始元で元の次数へ戻す。
規約：元の Hom 写像を保持する。使われ方：一般 kernel の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w) [DGCategory R C] [DGCategory R E]
/-- 実斉次 shift による全次数の cycle 比較。 -/
lemma dgFunctor_graded_cycle_lift (G : DGFunctor R C E) [G.onHomotopy.Full]
    {x w z : C} (n : ℤ) (f : GradedHom R x w n) (g : GradedHom R w x (-n))
    (hf : differential R f = 0) (hg : differential R g = 0)
    (h : GradedHom R x x (-1))
    (hh : (homObject R C x x).d (-1) 0 h =
      compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (a : GradedHom R (G.obj x) (G.obj z) n) (ha : differential R a = 0) :
    ∃ b : GradedHom R x z n, differential R b = 0 ∧
      ∃ t : GradedHom R (G.obj x) (G.obj z) (n - 1),
        (homObject R E (G.obj x) (G.obj z)).d (n - 1) n t = a - (G.map x z).f n b := by
  let F := (G.map x w).f n f
  let H := (G.map w x).f (-n) g
  have hF : differential R F = 0 := by rw [← map_differential G, hf, map_zero]
  have hH : differential R H = 0 := by rw [← map_differential G, hg, map_zero]
  have hhh : (homObject R E (G.obj x) (G.obj x)).d (-1) 0 ((G.map x x).f (-1) h) =
      compose R H F (add_neg_cancel n) - (unitElement R (G.obj x)).val := by
    calc
      _ = (G.map x x).f 0 ((homObject R C x x).d (-1) 0 h) :=
        ConcreteCategory.congr_hom ((G.map x x).comm (-1) 0) h
      _ = _ := by rw [hh, map_sub, DGNerve.map_compose, G.map_unitElement R]
  have hac : differential R (compose R a H (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hH, zero_compose, compose_zero, smul_zero, add_zero]
  obtain ⟨b, hb, t, ht⟩ := dgFunctor_zero_cycle_lift R C E G w z
    (compose R a H (neg_add_cancel n)) hac
  obtain ⟨e, he⟩ := dgGradedCycle_lift_recover R E n F H hF
    ((G.map x x).f (-1) h) hhh a ha ((G.map w z).f 0 b) t ht
  refine ⟨compose R b f (add_zero n), ?_, e, ?_⟩
  · rw [differential_compose, hb, hf, zero_compose, compose_zero, smul_zero, add_zero]
  · rw [DGNerve.map_compose]
    exact he
/-- 実斉次 shift による全次数の cycle 比較。 -/
lemma dgFunctor_graded_boundary_reflect (G : DGFunctor R C E) [G.onHomotopy.Faithful]
    {x w z : C} (n : ℤ) (f : GradedHom R x w n) (g : GradedHom R w x (-n))
    (hf : differential R f = 0) (hg : differential R g = 0)
    (h : GradedHom R x x (-1))
    (hh : (homObject R C x x).d (-1) 0 h =
      compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (a : GradedHom R x z n) (ha : differential R a = 0)
    (b : GradedHom R (G.obj x) (G.obj z) (n - 1))
    (hb : (homObject R E (G.obj x) (G.obj z)).d (n - 1) n b = (G.map x z).f n a) :
    ∃ t : GradedHom R x z (n - 1), (homObject R C x z).d (n - 1) n t = a := by
  have hac : differential R (compose R a g (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hg, zero_compose, compose_zero, smul_zero, add_zero]
  let H := (G.map w x).f (-n) g
  have hH : differential R H = 0 := by rw [← map_differential G, hg, map_zero]
  have hbt : (homObject R E (G.obj w) (G.obj z)).d (-1) 0
      (compose R b H (by omega)) =
        (G.map w z).f 0 (compose R a g (neg_add_cancel n)) := by
    rw [dgGradedBoundary_precompose_closed R E (r := n) _ (by decide) (by omega) H hH,
      hb, DGNerve.map_compose]
  obtain ⟨t, ht⟩ := dgFunctor_zero_boundary_reflect R C E G w z
    (compose R a g (neg_add_cancel n)) hac (compose R b H (by omega)) hbt
  obtain ⟨e, he⟩ := dgGradedCycle_lift_recover R C n f g hf h hh a ha 0 t (by
    simpa only [sub_zero] using ht)
  exact ⟨e, by simpa only [zero_compose, sub_zero] using he⟩
end SerrePositivity.InfinityCategories
