module
public import SerrePositivity.DifferentialGraded.Module.KernelCells

/-! # U10a4：全dg自然なcone延長とkernel内でのcycle消去 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} (f : M ⟶ N)
example : Small.{u} (ModuleKernelCellIndex A D f) := inferInstance
example : moduleKernelCellMap A D f ≫ f = 0 := moduleKernelCellMap_comp A D f
example : moduleKernelCellStepι A D f ≫ moduleKernelCellStepπ A D f = f :=
  moduleKernelCellStep_fac A D f
example (hf : moduleDegreewiseSurjective A D f) :
    moduleDegreewiseSurjective A D (moduleKernelCellStepπ A D f) :=
  moduleKernelCellStepπ_degreewiseSurjective A D f hf
example (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1))
    (hz : ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).X n,
      ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleKernelCellStepπ A D f)).f n t = 0 :=
  moduleKernelCellStep_killsInKernel A D f x n z hz
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complexConeDesc
#print axioms SerrePositivity.DifferentialGraded.complexConeDesc_f
#print axioms SerrePositivity.DifferentialGraded.complexConeDesc_ofHom
#print axioms SerrePositivity.DifferentialGraded.complexConeDesc_inr
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_desc
#print axioms SerrePositivity.DifferentialGraded.complexConeBoundaryWitness
#print axioms SerrePositivity.DifferentialGraded.complexConeBoundaryWitness_d
#print axioms SerrePositivity.DifferentialGraded.complexConeBoundaryWitness_desc
#print axioms SerrePositivity.DifferentialGraded.complexCone_inl_boundary
#print axioms SerrePositivity.DifferentialGraded.moduleCompZero_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeDesc
#print axioms SerrePositivity.DifferentialGraded.moduleConeDesc_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeDesc_inr
#print axioms SerrePositivity.DifferentialGraded.freeSphereHomEquiv_zero_val
#print axioms SerrePositivity.DifferentialGraded.ModuleKernelCellIndex
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellIndexSmall
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellFamily
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellSource
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellMap
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellι_map
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellMap_comp
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStep
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepι
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepπ
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStep_fac
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStepπ_degreewiseSurjective
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStep_killsInKernel
#print axioms SerrePositivity.DifferentialGraded.moduleKernelCellStep_kills
