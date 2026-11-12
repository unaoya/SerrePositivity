module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomotopyAdjunctionCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelResolutionHomotopyAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResolutionHomologyDetection
/-!
概要：一般 kernel の実出力分解に、全 Hom 準同型性を持つ実閉余単位を構成する。
方針：同じ telescope の H⁰ 随伴を実閉射で表し、実斉次 shift を全整数次数へ用いる。
規約：生の出力の射影性・分解圏の Small 性は不要。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実閉余単位の全入力の Hom 鎖写像は、全整数次数で準同型。 -/
lemma dgKernelResolutionCounit_quasiIso_exists (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) :
    ∃ (t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))
      (ε : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).obj t) ⟶
        ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y),
      ∀ x, QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) (t := t) (y := y)
        (closedHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).obj t))
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  obtain ⟨t, ε, hu⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyAdjunction_counit_closed_exists R C
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionHomotopyRightAdjoint R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionHomotopyAdjunction R D E P) y
  refine ⟨t, ε, fun x => ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn_quasiIso_of_gradedShifts R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G ε hu
  intro z n
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolution_gradedShiftHomotopyInverse R D E F z (-n)
  obtain ⟨w, f, g, hf, hg, h, hh, h', hh'⟩ := hs
  let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : _root_.SerrePositivity.DifferentialGraded.differential R f' = 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, hf, map_zero]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (_root_.SerrePositivity.DifferentialGraded.unitElement R z).val) hc)⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
