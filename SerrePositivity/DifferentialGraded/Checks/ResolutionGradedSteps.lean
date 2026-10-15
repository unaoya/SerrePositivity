module
public import SerrePositivity.DifferentialGraded.Module.ResolutionGradedSteps

/-! # U10a8：cell列の真の商とfiltrationの包含 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleGradedSplit A D (moduleKernelCellStepι A D f) (moduleKernelCellStepQuotient A D f) :=
  moduleKernelCellStepGradedSplit A D f
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (moduleKernelCellStepQuotient A D f)
      (moduleKernelCellStepGradedSplit A D f).inclusion_projection) :=
  moduleKernelCellStepCokernel A D f
example (M : ModuleCategory A D) (k : ℕ) : Mono (moduleResolutionCandidateι A D M k) :=
  moduleResolutionCandidateι_mono A D M k
example (M : ModuleCategory A D) (k : ℕ) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n) :=
  moduleResolutionCandidateι_degreewiseMono A D M k x n
example (M : ModuleCategory A D) (i j : ℕ) (h : i ≤ j) :
    Mono ((moduleResolutionDiagram A D M).map (homOfLE h)) :=
  moduleResolutionDiagram_map_mono A D M i j h
example (M : ModuleCategory A D) (i j : ℕ) (h : i ≤ j) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation A D x).map ((moduleResolutionDiagram A D M).map (homOfLE h))).f n) :=
  moduleResolutionDiagram_map_degreewiseMono A D M x n i j h
example (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n) :
    ∃ (k : ℕ) (t : ((moduleEvaluation A D x).obj (moduleResolutionStage A D M k).left).X n),
      ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n t = z :=
  moduleResolutionCandidate_element_rep A D M x n z
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepQuotient
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepGradedSplit
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepι_mono
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepCokernel
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionTransition_mono
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionDiagram_map_mono
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionDiagram_map_degreewiseMono
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateι_degreewiseMono
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidateι_mono

#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_element_rep
