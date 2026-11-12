module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorGradedCycleLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexCycleQuasiIsoCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResolutionGradedShift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomTransport
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
/-- 実斉次 shift と H⁰ の充満忠実性による全次数の検出。 -/
lemma dgFunctor_homQuasiIso_of_gradedShifts
    (C : Type v) (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) [G.onHomotopy.Full] [G.onHomotopy.Faithful]
    (hs : ∀ (x : C) (n : ℤ), ∃ (w : C) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w n)
      (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x (-n)), _root_.SerrePositivity.DifferentialGraded.differential R f = 0 ∧ _root_.SerrePositivity.DifferentialGraded.differential R g = 0 ∧
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
        _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val) : HomQuasiIso G := by
  intro x z
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIso_of_cycle_lift_boundary_reflect R
  · intro q a ha
    obtain ⟨w, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_graded_cycle_lift R C E G (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl
  · intro q a ha b hb
    obtain ⟨w, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_graded_boundary_reflect R C E G (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl b hb
/-- 実斉次 shift と H⁰ の充満忠実性による全次数の検出。 -/
lemma dgModuleResolution_homQuasiIso_of_ho
    (B : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [Small.{u} B]
    (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) (RightModule R E))
    (T : Type t) [_root_.SerrePositivity.DifferentialGraded.DGCategory R T]
    (G : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F) T)
    [G.onHomotopy.Full] [G.onHomotopy.Faithful] : HomQuasiIso G := by
  apply dgFunctor_homQuasiIso_of_gradedShifts R _ T G
  intro x n
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolution_gradedShiftHomotopyInverse R B E F x (-n)
  obtain ⟨w, f, g, hf, hg, h, hh, h', hh'⟩ := hs
  let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : _root_.SerrePositivity.DifferentialGraded.differential R f' = 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, hf, map_zero]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val) hc)⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
