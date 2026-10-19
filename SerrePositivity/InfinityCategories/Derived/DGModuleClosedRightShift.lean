module
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomRightShift
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition

/-! # 斉次閉加群 Hom からシフトへの実閉射

概要：斉次閉元を標的のシフトへの閉加群射へ送り、前合成の成分を照合する。
方針：次数零 cycle の閉射表示と、斉次 shift の包含による合成の結合則を使う。
規約：斉次元と閉射の cycle は厳密に一致する。使われ方：β3 の全次数の零化の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 斉次閉元が定める標的の整数シフトへの閉加群射。 -/
def dgModuleClosedRightShift {M N : ModuleCategory A D} (n : ℤ)
    (f : GradedHom A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) n) (hf : differential A f = 0) : M ⟶ N⟦n⟧ :=
  moduleMorphismOfCycle A D (dgModuleHomRightShift A D n f)
    (dgModuleHomRightShift_closed A D n f hf)

/-- 作った閉射の cycle は包含による斉次合成そのもの。 -/
lemma dgModuleClosedRightShift_cycle {M N : ModuleCategory A D} (n : ℤ) (f) (hf) :
    (closedHomEquiv A (RightModule A D) M (N⟦n⟧)
      (dgModuleClosedRightShift A D n f hf)).val = dgModuleHomRightShift A D n f :=
  moduleMorphismOfCycle_cycle A D _ _

/-- 右シフトの斉次操作は閉次数零元の前合成と厳密に両立する。 -/
lemma dgModuleHomRightShift_precompose {L M N : RightModule A D} (n : ℤ)
    (f : GradedHom A M N n) (g : GradedHom A L M 0) :
    dgModuleHomRightShift A D n (compose A f g (zero_add n)) =
      compose A (dgModuleHomRightShift A D n f) g (by decide) := by
  exact compose_assoc_of_sum g f (moduleShiftInElement A D n N)
    (zero_add n) (add_neg_cancel n) (add_neg_cancel n)

/-- 閉射を前合成した shift 閉射の cycle は、元の斉次前合成の右シフト。 -/
lemma dgModuleClosedRightShift_precompose_cycle {L M N : ModuleCategory A D} (n : ℤ)
    (f : GradedHom A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) n) (hf : differential A f = 0) (g : L ⟶ M) :
    (closedHomEquiv A (RightModule A D) L (N⟦n⟧)
      (g ≫ dgModuleClosedRightShift A D n f hf)).val =
        dgModuleHomRightShift A D n (compose A f
          (closedHomEquiv A (RightModule A D) L M g).val (zero_add n)) := by
  rw [closedHom_comp, dgModuleClosedRightShift_cycle, dgModuleHomRightShift_precompose]

end SerrePositivity.InfinityCategories
