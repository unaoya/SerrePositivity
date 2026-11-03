module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a12：shiftと自由なcell商 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (x : D) (n s : ℤ) : (freeSphere A D x n)⟦s⟧ ≅ freeSphere A D x (n - s) :=
  freeSphereShiftIso A D x n s
example {J : Type w} [Small.{u} J] (x : J → D) (n : J → ℤ) (s : ℤ) :
    (∐ fun t => freeSphere A D (x t) (n t))⟦s⟧ ≅
      ∐ fun t => freeSphere A D (x t) (n t - s) :=
  freeSphereCoproductShiftIso A D x n s
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleKernelCellSource A D f)⟦(1 : ℤ)⟧ ≅ ∐ moduleKernelCellQuotientFamily A D f :=
  moduleKernelCellQuotientFreeIso A D f
example (K : Complex A) (M : RightModule A D) (s : ℤ) :
    ForgetEnrichment.of (Complex A) (tensorModule (K⟦s⟧) M) ≅
      (ForgetEnrichment.of (Complex A) (tensorModule K M))⟦s⟧ :=
  tensorModuleShiftIso A D K M s
example : (freeSphere ℤ PUnit.{1} PUnit.unit (-2))⟦(1 : ℤ)⟧ ≅
    freeSphere ℤ PUnit.{1} PUnit.unit (-3) := freeSphereShiftIso ℤ PUnit.{1} PUnit.unit (-2) 1
example : (freeSphere (ZMod 2) PUnit.{1} PUnit.unit 1)⟦(-1 : ℤ)⟧ ≅
    freeSphere (ZMod 2) PUnit.{1} PUnit.unit 2 :=
  freeSphereShiftIso (ZMod 2) PUnit.{1} PUnit.unit 1 (-1)
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.tensorShiftLeft_apply
#print axioms SerrePositivity.DifferentialGraded.tensorShiftLeft_hom_naturality
#print axioms SerrePositivity.DifferentialGraded.tensorModuleShiftIso
#print axioms SerrePositivity.DifferentialGraded.tensorModuleShiftIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.tensorModuleShiftIso_inv_eval
#print axioms SerrePositivity.DifferentialGraded.freeAtShiftIso
#print axioms SerrePositivity.DifferentialGraded.complexSphereShiftIso
#print axioms SerrePositivity.DifferentialGraded.freeSphereShiftIso
#print axioms SerrePositivity.DifferentialGraded.moduleShiftCoproductIso
#print axioms SerrePositivity.DifferentialGraded.freeSphereCoproductShiftIso
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellQuotientFamily
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellQuotientFreeIso
