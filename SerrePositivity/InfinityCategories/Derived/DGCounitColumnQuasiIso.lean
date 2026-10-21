module
public import SerrePositivity.InfinityCategories.Derived.DGCounitColumnZeroLifting
public import SerrePositivity.InfinityCategories.Derived.DGCounitColumnGradedLifting
public import SerrePositivity.InfinityCategories.Derived.ComplexCycleQuasiIsoCriterion
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [DGCategory R C] [DGCategory R E]
/-- 同じ余単位の H⁰ 普遍性を全整数次数の Hom 準同型性へ昇格する。 -/
lemma dgCounitColumn_quasiIso_of_gradedShifts (G : DGFunctor R C E) {t : C} {y : E}
    (ε : ForgetEnrichment.of (Complex R) (G.obj t) ⟶ ForgetEnrichment.of (Complex R) y)
    (hu : ∀ x : C, Function.Bijective (fun f :
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x) ⟶
        (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) t) =>
      G.onHomotopy.map f ≫ (toHomotopy R E).map ε))
    (hs : ∀ (x : C) (n : ℤ), ∃ (z : C) (f : GradedHom R x z n)
      (g : GradedHom R z x (-n)), differential R f = 0 ∧ differential R g = 0 ∧
      ∃ h : GradedHom R x x (-1), (homObject R C x x).d (-1) 0 h =
        compose R g f (add_neg_cancel n) - (unitElement R x).val)
    (x : C) : QuasiIso (dgCounitColumn R C E G (t := t) (y := y)
      (closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj t))
        (ForgetEnrichment.of (Complex R) y) ε) x) := by
  let e := closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj t))
    (ForgetEnrichment.of (Complex R) y) ε
  have hz := dgCounitColumn_zero_cycle_lift R C E G ε (fun z => (hu z).surjective)
  have hi := dgCounitColumn_zero_boundary_reflect R C E G ε (fun z => (hu z).injective)
  apply complexQuasiIso_of_cycle_lift_boundary_reflect R
  · intro q a ha
    obtain ⟨z, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := dgCounitColumn_graded_cycle_lift R C E G e hz (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl
  · intro q a ha b hb
    obtain ⟨z, f, g, hf, hg, h, hh⟩ := hs x (q + 1)
    have hl := dgCounitColumn_graded_boundary_reflect R C E G e hi
      (q + 1) f g hf hg h hh a ha
    have hn : q + 1 - 1 = q := by omega
    rw [hn] at hl
    exact hl b hb
end SerrePositivity.InfinityCategories
