module
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # U10b4c：Hom短完全列とsemifree有限段の受入検査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    (s.homShortComplex T).ShortExact := s.homShortComplex_shortExact T

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q)
    (hz : (eHomWhiskerRight (Complex A) f T).f q z = 0) :
    (eHomWhiskerRight (Complex A) g T).f q (s.homKernelRetraction T q z) = z :=
  s.homKernel_of_restriction_zero T q z hz

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (hM : moduleHomotopicallyProjective A D M)
    (hP : moduleHomotopicallyProjective A D P) : moduleHomotopicallyProjective A D N :=
  s.homotopicallyProjective A D hM hP

example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.stage n) := F.stage_homotopicallyProjective A D n

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms ModuleGradedSplit.homKernelRetraction
#print axioms ModuleGradedSplit.homKernelRetraction_π
#print axioms ModuleGradedSplit.homKernel_retraction
#print axioms ModuleGradedSplit.homKernel_injective
#print axioms ModuleGradedSplit.homKernel_of_restriction_zero
#print axioms ModuleGradedSplit.homKernel_restriction_zero
#print axioms ModuleGradedSplit.homShortComplex
#print axioms ModuleGradedSplit.homShortComplex_degreewise_shortExact
#print axioms ModuleGradedSplit.homShortComplex_shortExact
#print axioms ModuleGradedSplit.homotopicallyProjective
#print axioms ModuleSemifreeFiltration.stage_homotopicallyProjective
