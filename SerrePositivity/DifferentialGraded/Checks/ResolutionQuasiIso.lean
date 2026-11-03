module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a6：可算cell候補のobjectwise準同型性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleResolutionCandidateπ A D M) :=
  moduleResolutionCandidateπ_quasiIso A D M
example (M : ModuleCategory A D) :
    (freeCellBoundaries A D).rlp (moduleResolutionCandidateπ A D M) :=
  (freeCellBoundaries_rlp_eq A D).symm ▸
    ⟨moduleResolutionCandidateπ_degreewiseSurjective A D M,
      moduleResolutionCandidateπ_quasiIso A D M⟩
example (M : ModuleCategory A D) (x : D) (n : ℤ) :
    moduleBoundaryLiftAt A D x n (moduleResolutionCandidateπ A D M) :=
  moduleResolutionCandidate_boundaryLift A D M x n
example (M : ModuleCategory ℤ PUnit.{1}) :
    moduleQuasiIso ℤ PUnit.{1} (moduleResolutionCandidateπ ℤ PUnit.{1} M) :=
  moduleResolutionCandidateπ_quasiIso ℤ PUnit.{1} M
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    moduleQuasiIso (ZMod 2) PUnit.{1} (moduleResolutionCandidateπ (ZMod 2) PUnit.{1} M) :=
  moduleResolutionCandidateπ_quasiIso (ZMod 2) PUnit.{1} M
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complexSequentialColimit_cycle_rep
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_cycle_rep
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_kernelCycle_boundary
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_boundaryLift
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ_quasiIso
