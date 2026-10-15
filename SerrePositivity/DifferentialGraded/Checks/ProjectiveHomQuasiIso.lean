module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso

/-! # U10b6d：全Homの指定quasiIso不変性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {T M N : ModuleCategory A D} (hT : moduleHomotopicallyProjective A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso (eHomWhiskerLeft (Complex A) T f) :=
  moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf

example {T M N : ModuleCategory A D} (hT : moduleSemifree A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso (eHomWhiskerLeft (Complex A) T f) := moduleSemifree_postcompose_quasiIso A D hT f hf

example (T M : ModuleCategory A D) :
    QuasiIso (eHomWhiskerLeft (Complex A) (moduleResolutionCandidate A D T)
      (moduleResolutionCandidateπ A D M)) :=
  moduleSemifree_postcompose_quasiIso A D (moduleResolutionCandidate_semifree A D T)
    (moduleResolutionCandidateπ A D M) (moduleResolutionCandidateπ_quasiIso A D M)

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleHomotopicallyProjective_postcompose_quasiIso
#print axioms moduleSemifree_postcompose_quasiIso
