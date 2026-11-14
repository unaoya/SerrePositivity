module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCounitColumn
/-!
概要：余単位による Hom 鎖写像の次数零の検査を全整数次数へ戻す。
方針：実斉次 shift と単位差の境界原始元を使い、同じ cycle と原始元を回収する。
規約：高次 Hom を省略しない。使われ方：一般 RHom の全写像空間の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
variable (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) {t : C} {y : E}
  (ε : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj t) y))
/-- 実斉次 shift に沿い、次数零の余単位の cycle 比較を全次数へ戻す。 -/
lemma dgCounitColumn_graded_cycle_lift
    (hs : ∀ z : C, ∀ a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj z) y 0, _root_.SerrePositivity.DifferentialGraded.differential R a = 0 →
      ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom R z t 0, _root_.SerrePositivity.DifferentialGraded.differential R b = 0 ∧
        ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj z) y (-1),
          (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj z) y).d (-1) 0 h =
            a - (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε z).f 0 b)
    {x z : C} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R z x (-n))
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
      _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0) :
    ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t n, _root_.SerrePositivity.DifferentialGraded.differential R b = 0 ∧
      ∃ k : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y (n - 1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (n - 1) n k =
          a - (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε x).f n b := by
  let F := (G.map x z).f n f
  let H := (G.map z x).f (-n) g
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
  obtain ⟨b, hb, k, hk⟩ := hs z (_root_.SerrePositivity.DifferentialGraded.compose R a H (neg_add_cancel n)) hac
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedCycle_lift_recover R E n F H hF
    ((G.map x x).f (-1) h) hhh a ha ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε z).f 0 b) k hk
  refine ⟨_root_.SerrePositivity.DifferentialGraded.compose R b f (add_zero n), ?_, e, ?_⟩
  · rw [differential_compose, hb, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_compose]
    exact he
/-- 実斉次 shift に沿い、次数零の余単位の境界反映を全次数へ戻す。 -/
lemma dgCounitColumn_graded_boundary_reflect
    (hi : ∀ z : C, ∀ a : _root_.SerrePositivity.DifferentialGraded.GradedHom R z t 0, _root_.SerrePositivity.DifferentialGraded.differential R a = 0 →
      ∀ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj z) y (-1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj z) y).d (-1) 0 h =
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε z).f 0 a →
        ∃ k : _root_.SerrePositivity.DifferentialGraded.GradedHom R z t (-1), (_root_.SerrePositivity.DifferentialGraded.homObject R C z t).d (-1) 0 k = a)
    {x z : C} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R z x (-n))
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
      _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y (n - 1))
    (hb : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (n - 1) n b =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε x).f n a) :
    ∃ k : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t (n - 1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x t).d (n - 1) n k = a := by
  have hac : _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  let H := (G.map z x).f (-n) g
  have hH : differential R H = 0 := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential G, hg, map_zero]
  have hbt : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj z) y).d (-1) 0
      (_root_.SerrePositivity.DifferentialGraded.compose R b H (by omega)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G ε z).f 0 (compose R a g (neg_add_cancel n)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedBoundary_precompose_closed R E (r := n) _ (by decide) (by omega) H hH,
      hb, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_compose]
  obtain ⟨k, hk⟩ := hi z (_root_.SerrePositivity.DifferentialGraded.compose R a g (neg_add_cancel n)) hac
    (_root_.SerrePositivity.DifferentialGraded.compose R b H (by omega)) hbt
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedCycle_lift_recover R C n f g hf h hh a ha 0 k (by
    simpa only [sub_zero] using hk)
  exact ⟨e, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero] using he⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
