module
public import SerrePositivity.InfinityCategories.Derived.DGCounitColumn
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [DGCategory R C] [DGCategory R E]
variable (G : DGFunctor R C E) {t : C} {y : E}
  (ε : zeroCycles (homObject R E (G.obj t) y))
/-- 実斉次 shift に沿い、次数零の余単位の cycle 比較を全次数へ戻す。 -/
lemma dgCounitColumn_graded_cycle_lift
    (hs : ∀ z : C, ∀ a : GradedHom R (G.obj z) y 0, differential R a = 0 →
      ∃ b : GradedHom R z t 0, differential R b = 0 ∧
        ∃ h : GradedHom R (G.obj z) y (-1),
          (homObject R E (G.obj z) y).d (-1) 0 h =
            a - (dgCounitColumn R C E G ε z).f 0 b)
    {x z : C} (n : ℤ) (f : GradedHom R x z n) (g : GradedHom R z x (-n))
    (hf : differential R f = 0) (hg : differential R g = 0)
    (h : GradedHom R x x (-1))
    (hh : (homObject R C x x).d (-1) 0 h =
      compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (a : GradedHom R (G.obj x) y n) (ha : differential R a = 0) :
    ∃ b : GradedHom R x t n, differential R b = 0 ∧
      ∃ k : GradedHom R (G.obj x) y (n - 1),
        (homObject R E (G.obj x) y).d (n - 1) n k =
          a - (dgCounitColumn R C E G ε x).f n b := by
  let F := (G.map x z).f n f
  let H := (G.map z x).f (-n) g
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
  obtain ⟨b, hb, k, hk⟩ := hs z (compose R a H (neg_add_cancel n)) hac
  obtain ⟨e, he⟩ := dgGradedCycle_lift_recover R E n F H hF
    ((G.map x x).f (-1) h) hhh a ha ((dgCounitColumn R C E G ε z).f 0 b) k hk
  refine ⟨compose R b f (add_zero n), ?_, e, ?_⟩
  · rw [differential_compose, hb, hf, zero_compose, compose_zero, smul_zero, add_zero]
  · rw [dgCounitColumn_compose]
    exact he
/-- 実斉次 shift に沿い、次数零の余単位の境界反映を全次数へ戻す。 -/
lemma dgCounitColumn_graded_boundary_reflect
    (hi : ∀ z : C, ∀ a : GradedHom R z t 0, differential R a = 0 →
      ∀ h : GradedHom R (G.obj z) y (-1),
        (homObject R E (G.obj z) y).d (-1) 0 h =
          (dgCounitColumn R C E G ε z).f 0 a →
        ∃ k : GradedHom R z t (-1), (homObject R C z t).d (-1) 0 k = a)
    {x z : C} (n : ℤ) (f : GradedHom R x z n) (g : GradedHom R z x (-n))
    (hf : differential R f = 0) (hg : differential R g = 0)
    (h : GradedHom R x x (-1))
    (hh : (homObject R C x x).d (-1) 0 h =
      compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (a : GradedHom R x t n) (ha : differential R a = 0)
    (b : GradedHom R (G.obj x) y (n - 1))
    (hb : (homObject R E (G.obj x) y).d (n - 1) n b =
      (dgCounitColumn R C E G ε x).f n a) :
    ∃ k : GradedHom R x t (n - 1), (homObject R C x t).d (n - 1) n k = a := by
  have hac : differential R (compose R a g (neg_add_cancel n)) = 0 := by
    rw [differential_compose, ha, hg, zero_compose, compose_zero, smul_zero, add_zero]
  let H := (G.map z x).f (-n) g
  have hH : differential R H = 0 := by rw [← map_differential G, hg, map_zero]
  have hbt : (homObject R E (G.obj z) y).d (-1) 0
      (compose R b H (by omega)) =
        (dgCounitColumn R C E G ε z).f 0 (compose R a g (neg_add_cancel n)) := by
    rw [dgGradedBoundary_precompose_closed R E (r := n) _ (by decide) (by omega) H hH,
      hb, dgCounitColumn_compose]
  obtain ⟨k, hk⟩ := hi z (compose R a g (neg_add_cancel n)) hac
    (compose R b H (by omega)) hbt
  obtain ⟨e, he⟩ := dgGradedCycle_lift_recover R C n f g hf h hh a ha 0 k (by
    simpa only [sub_zero] using hk)
  exact ⟨e, by simpa only [zero_compose, sub_zero] using he⟩
end SerrePositivity.InfinityCategories
