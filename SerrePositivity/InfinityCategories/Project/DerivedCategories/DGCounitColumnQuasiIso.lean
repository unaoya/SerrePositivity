module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCounitColumnZeroLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCounitColumnGradedLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexCycleQuasiIsoCriterion
/-!
概要：斉次シフトを持つ実 dg 圏で、余単位の H⁰ 普遍性から全 Hom 準同型性を得る。
方針：零 cycle の持ち上げ・境界反映を全整数次数へ戻し、実写像錐を検査する。
規約：元の余単位の鎖写像を保持する。使われ方：一般 RHom の全写像空間の普遍性。
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
/-- 同じ余単位の H⁰ 普遍性を全整数次数の Hom 準同型性へ昇格する。 -/
lemma dgCounitColumn_quasiIso_of_gradedShifts (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) {t : C} {y : E}
    (ε : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t) ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (hu : ∀ x : C, Function.Bijective (fun f :
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) ⟶
        (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) =>
      G.onHomotopy.map f ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε))
    (hs : ∀ (x : C) (n : ℤ), ∃ (z : C) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z n)
      (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R z x (-n)), _root_.SerrePositivity.DifferentialGraded.differential R f = 0 ∧ _root_.SerrePositivity.DifferentialGraded.differential R g = 0 ∧
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
        _root_.SerrePositivity.DifferentialGraded.compose R g f (add_neg_cancel n) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (x : C) : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y)
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t))
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x) := by
  let e := _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_zero_cycle_lift R C E G ε (fun z => (hu z).surjective)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_zero_boundary_reflect R C E G ε (fun z => (hu z).injective)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIso_of_cycle_lift_boundary_reflect R
  · intro q a ha
    obtain ⟨z, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_graded_cycle_lift R C E G e hz (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl
  · intro q a ha b hb
    obtain ⟨z, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_graded_boundary_reflect R C E G e hi
      (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl b hb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
