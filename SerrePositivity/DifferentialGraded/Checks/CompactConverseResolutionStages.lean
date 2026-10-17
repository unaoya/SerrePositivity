module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseResolutionStages

/-! # 標準解像度の有限因子分解の監査 -/
@[expose] public section
noncomputable section
universe u v
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleCategory A D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) :=
  moduleFiniteCellFactorTarget_resolutionStage A D M n

#print axioms moduleFiniteCellOver_freeSphere
#print axioms moduleFiniteCellFactorTarget_coproduct_small
#print axioms moduleFiniteCellFactorTarget_projectiveCoproduct
#print axioms moduleFiniteCellFactorTarget_sphereCoproduct
#print axioms moduleFiniteCellFactorTarget_resolutionStage
