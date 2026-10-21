module
public import SerrePositivity.InfinityCategories.Derived.DGHomotopyAdjunctionCounit
public import SerrePositivity.InfinityCategories.Derived.DGKernelResolutionHomotopyAdjunction
public import SerrePositivity.InfinityCategories.Derived.DGResolutionHomologyDetection
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ実閉余単位の全入力の Hom 鎖写像は、全整数次数で準同型。 -/
lemma dgKernelResolutionCounit_quasiIso_exists (P : Bimodule R E D)
    (y : SemifreeDGModules R E) :
    ∃ (t : DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P))
      (ε : ForgetEnrichment.of (Complex R)
          ((dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
            (dgSemifreeKernelModuleDG R D E P)).obj t) ⟶
        ForgetEnrichment.of (Complex R) y),
      ∀ x, QuasiIso (dgCounitColumn R _ (SemifreeDGModules R E)
        (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
          (dgSemifreeKernelModuleDG R D E P)) (t := t) (y := y)
        (closedHomEquiv R (SemifreeDGModules R E)
          (ForgetEnrichment.of (Complex R)
            ((dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
              (dgSemifreeKernelModuleDG R D E P)).obj t))
          (ForgetEnrichment.of (Complex R) y) ε) x) := by
  let F := dgSemifreeKernelModuleDG R D E P
  let C := DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E F
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  obtain ⟨t, ε, hu⟩ := dgHomotopyAdjunction_counit_closed_exists R C
    (SemifreeDGModules R E) G (dgKernelResolutionHomotopyRightAdjoint R D E P)
      (dgKernelResolutionHomotopyAdjunction R D E P) y
  refine ⟨t, ε, fun x => ?_⟩
  apply dgCounitColumn_quasiIso_of_gradedShifts R C (SemifreeDGModules R E) G ε hu
  intro z n
  have hs := dgModuleResolution_gradedShiftHomotopyInverse R D E F z (-n)
  obtain ⟨w, f, g, hf, hg, h, hh, h', hh'⟩ := hs
  let f' := gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : differential R f' = 0 := by
    rw [← gradedHomTransport_differential, hf, map_zero]
  have hc := gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (unitElement R z).val) hc)⟩
end SerrePositivity.InfinityCategories
