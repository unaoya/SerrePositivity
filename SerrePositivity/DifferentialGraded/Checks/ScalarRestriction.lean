module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import Mathlib.Data.ZMod.Basic

/-! # dg 係数制限の型検査と公理監査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example : ModuleCategory (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit) ⥤
    ModuleCategory ℤ PUnit := moduleRestriction (Int.castRingHom (ZMod 2)) PUnit

#print axioms restrictionHom
#print axioms restriction_μ_apply
#print axioms restriction_ε_one
#print axioms restrictionHom_identity
#print axioms restrictionHom_composition
#print axioms restrictionComplexDGFunctor
#print axioms restrictDGFunctor
#print axioms unitDGFunctor
#print axioms oppositeDGInverse
#print axioms rightRestriction
#print axioms leftRestriction
#print axioms rightRestriction_action
#print axioms restrictionHom_postcompose
#print axioms restrictionHom_precompose
#print axioms moduleRestrictionMap
#print axioms moduleRestriction
#print axioms moduleRestrictionEvaluationIso

end SerrePositivity.DifferentialGraded.ScalarExtension
