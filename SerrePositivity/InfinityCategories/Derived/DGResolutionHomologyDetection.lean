module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorGradedCycleLifting
public import SerrePositivity.InfinityCategories.Derived.ComplexCycleQuasiIsoCriterion
public import SerrePositivity.InfinityCategories.Derived.DGResolutionGradedShift
public import SerrePositivity.InfinityCategories.DGNerve.HomTransport
/-!
概要：実斉次 shift を持つ dg 圏で、H⁰ の充満忠実性から全 Hom 準同型性を得る。
方針：全次数 cycle の持ち上げ・境界反映から実写像錐の非輪状性を検査する。
規約：高次 Hom を省略しない。使われ方：実出力分解から一般 Morita の ∞ 同値へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R]
/-- 実斉次 shift と H⁰ の充満忠実性による全次数の検出。 -/
lemma dgFunctor_homQuasiIso_of_gradedShifts
    (C : Type v) (E : Type w) [DGCategory R C] [DGCategory R E]
    (G : DGFunctor R C E) [G.onHomotopy.Full] [G.onHomotopy.Faithful]
    (hs : ∀ (x : C) (n : ℤ), ∃ (w : C) (f : GradedHom R x w n)
      (g : GradedHom R w x (-n)), differential R f = 0 ∧ differential R g = 0 ∧
      ∃ h : GradedHom R x x (-1), (homObject R C x x).d (-1) 0 h =
        compose R g f (add_neg_cancel n) - (unitElement R x).val) : HomQuasiIso G := by
  intro x z
  apply complexQuasiIso_of_cycle_lift_boundary_reflect R
  · intro q a ha
    obtain ⟨w, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := dgFunctor_graded_cycle_lift R C E G (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl
  · intro q a ha b hb
    obtain ⟨w, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := dgFunctor_graded_boundary_reflect R C E G (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl b hb
/-- 実斉次 shift と H⁰ の充満忠実性による全次数の検出。 -/
lemma dgModuleResolution_homQuasiIso_of_ho
    (B : Type v) [DGCategory R B] [Small.{u} B]
    (E : Type w) [DGCategory R E] [Small.{u} E]
    (F : DGFunctor R (SemifreeDGModules R B) (RightModule R E))
    (T : Type t) [DGCategory R T]
    (G : DGFunctor R (DGModuleFunctorResolutionObject R (SemifreeDGModules R B) E F) T)
    [G.onHomotopy.Full] [G.onHomotopy.Faithful] : HomQuasiIso G := by
  apply dgFunctor_homQuasiIso_of_gradedShifts R _ T G
  intro x n
  have hs := dgModuleResolution_gradedShiftHomotopyInverse R B E F x (-n)
  obtain ⟨w, f, g, hf, hg, h, hh, h', hh'⟩ := hs
  let f' := gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : differential R f' = 0 := by
    rw [← gradedHomTransport_differential, hf, map_zero]
  have hc := gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (unitElement R x).val) hc)⟩
end SerrePositivity.InfinityCategories
