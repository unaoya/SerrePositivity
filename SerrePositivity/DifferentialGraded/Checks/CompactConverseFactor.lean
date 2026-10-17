module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseExtensions

/-! # compact 有限因子分解と Neeman 型拡大閉性の監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : (moduleFiniteCellFactorTarget A D S).IsTriangulated := inferInstance
example (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ ModuleFiniteCellFactor A D S (𝟙 X) :=
  modulePerfectOver_iff_id_finiteCellFactor A D S X

#print axioms moduleFiniteCellFactor_zero
#print axioms ModuleFiniteCellFactor.add
#print axioms ModuleFiniteCellFactor.precompose
#print axioms ModuleFiniteCellFactor.postcompose
#print axioms ModuleFiniteCellFactor.shift
#print axioms moduleFiniteCellFactor_sum
#print axioms moduleCompact_coproduct_finiteCellFactor
#print axioms modulePerfectOver_iff_id_finiteCellFactor
#print axioms moduleFiniteCellFactorTarget_of_finiteCell
#print axioms moduleFiniteCellFactorTarget_shift
#print axioms moduleFiniteCellFactorTarget_coproduct
#print axioms moduleFiniteCellFactorTarget_triangle_obj₂
#print axioms moduleFiniteCellFactorTargetIsTriangulated
#print axioms moduleFiniteCellFactorTarget_telescope
#print axioms modulePerfectOver_of_compact_factorTarget
