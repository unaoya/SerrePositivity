module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a11：初期自由disk被覆全体の二段分解 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : ModuleCategory A D) :
    ModuleGradedSplit A D (moduleDiskCoverBoundary A D M) (moduleDiskCoverQuotient A D M) :=
  moduleDiskCoverGradedSplit A D M
example (M : ModuleCategory A D) : Mono (moduleDiskCoverBoundary A D M) :=
  moduleDiskCoverBoundary_mono A D M
example (M : ModuleCategory A D) : Epi (moduleDiskCoverQuotient A D M) :=
  moduleDiskCoverQuotient_epi A D M
example (M : ModuleCategory A D) :
    IsColimit (CokernelCofork.ofπ (moduleDiskCoverQuotient A D M)
      (moduleDiskCoverGradedSplit A D M).inclusion_projection) :=
  moduleDiskCoverSphereCokernel A D M
example (M : ModuleCategory A D) (x : D) (n : ℤ) :
    ((moduleDiskCoverGradedSplit A D M).evaluationShortComplex x n).ShortExact :=
  (moduleDiskCoverGradedSplit A D M).evaluationShortExact x n
example (M : ModuleCategory ℤ PUnit.{1}) : Mono (moduleDiskCoverBoundary ℤ PUnit.{1} M) :=
  moduleDiskCoverBoundary_mono ℤ PUnit.{1} M
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    Epi (moduleDiskCoverQuotient (ZMod 2) PUnit.{1} M) :=
  moduleDiskCoverQuotient_epi (ZMod 2) PUnit.{1} M
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverUpperFamily
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverLowerFamily
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverBoundary
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverQuotient
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverGradedSplit
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverBoundary_mono
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverQuotient_epi
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverSphereCokernel
