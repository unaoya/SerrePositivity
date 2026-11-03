module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-! # U10a5：可算cell列と有限段kernel cycleの消去 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : ModuleCategory A D) (k : ℕ) :
    moduleDegreewiseSurjective A D (moduleResolutionStage A D M k).hom :=
  moduleResolutionStage_degreewiseSurjective A D M k
example (M : ModuleCategory A D) :
    moduleDegreewiseSurjective A D (moduleResolutionCandidateπ A D M) :=
  moduleResolutionCandidateπ_degreewiseSurjective A D M
example (M : ModuleCategory A D) (k : ℕ) :
    moduleResolutionCandidateι A D M k ≫ moduleResolutionCandidateπ A D M =
      (moduleResolutionStage A D M k).hom := moduleResolutionCandidateι_π A D M k
example (M : ModuleCategory A D) (k : ℕ) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj
      (moduleResolutionStage A D M k).left) (n + 1))
    (hz : ((moduleEvaluation A D x).map (moduleResolutionStage A D M k).hom).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n,
      ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f n t = 0 :=
  moduleResolutionCandidate_killsStage A D M k x n z hz
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleResolutionStage
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionTransition
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionStage_degreewiseSurjective
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionOverDiagram
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionDiagram
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCocone
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateι
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateι_π
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateι_succ
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ_degreewiseSurjective
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_killsStage
