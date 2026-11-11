module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroCycleLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedCycleRecovery
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 実斉次 shift による全次数の cycle 比較。 -/
lemma dgFunctor_graded_cycle_lift (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) [G.onHomotopy.Full]
    {x w z : C} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w n) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x (-n))
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
      _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) (G.obj z) n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0) :
    ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n, _root_.SerrePositivity.DifferentialGraded.differential R b = 0 ∧
      ∃ t : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) (G.obj z) (n - 1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) (G.obj z)).d (n - 1) n t = a - (G.map x z).f n b := by
  let F := (G.map x w).f n f
  let H := (G.map w x).f (-n) g
  have hF : differential R F = 0 := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential G, hf, map_zero]
  have hH : differential R H = 0 := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential G, hg, map_zero]
  have hhh : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) (G.obj x)).d (-1) 0 ((G.map x x).f (-1) h) =
      _root_.SerrePositivity.DifferentialGraded.compose R H F (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R (G.obj x)).val := by
    calc
      _ = (G.map x x).f 0 ((_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h) :=
        ConcreteCategory.congr_hom ((G.map x x).comm (-1) 0) h
      _ = _ := by rw [hh, map_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, G.map_unitElement R]
  have hac : _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.DifferentialGraded.compose R a H (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hH, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  obtain ⟨b, hb, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_zero_cycle_lift R C E G w z
    (_root_.SerrePositivity.DifferentialGraded.compose R a H (neg_add_cancel n)) hac
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedCycle_lift_recover R E n F H hF
    ((G.map x x).f (-1) h) hhh a ha ((G.map w z).f 0 b) t ht
  refine ⟨_root_.SerrePositivity.DifferentialGraded.compose R b f (add_zero n), ?_, e, ?_⟩
  · rw [differential_compose, hb, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
    exact he
/-- 実斉次 shift による全次数の cycle 比較。 -/
lemma dgFunctor_graded_boundary_reflect (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) [G.onHomotopy.Faithful]
    {x w z : C} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w n) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x (-n))
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
      _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) (G.obj z) (n - 1))
    (hb : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) (G.obj z)).d (n - 1) n b = (G.map x z).f n a) :
    ∃ t : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z (n - 1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x z).d (n - 1) n t = a := by
  have hac : _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  let H := (G.map w x).f (-n) g
  have hH : differential R H = 0 := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential G, hg, map_zero]
  have hbt : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj w) (G.obj z)).d (-1) 0
      (_root_.SerrePositivity.DifferentialGraded.compose R b H (by omega)) =
        (G.map w z).f 0 (_root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedBoundary_precompose_closed R E (r := n) _ (by decide) (by omega) H hH,
      hb, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_zero_boundary_reflect R C E G w z
    (_root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n)) hac (_root_.SerrePositivity.DifferentialGraded.compose R b H (by omega)) hbt
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedCycle_lift_recover R C n f g hf h hh a ha 0 t (by
    simpa only [sub_zero] using ht)
  exact ⟨e, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero] using he⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
