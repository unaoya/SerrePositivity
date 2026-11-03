module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import Mathlib.Data.ZMod.Basic

@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example : DerivedModuleCategory ℤ PUnit.{1} ⥤
    DerivedModuleCategory (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit.{1}) :=
  derivedExtension (Int.castRingHom (ZMod 2)) PUnit.{1}

#print axioms moduleExtension_cylinder_quasiIso
#print axioms moduleExtension_equalizes_boundary
#print axioms moduleExtensionHomotopyToDerived
#print axioms moduleExtension_map_eq_of_homotopy
#print axioms resolutionDerivedExtension
#print axioms derivedExtension
#print axioms resolutionDerivedExtensionComputation
#print axioms resolutionDerivedExtensionIso
#print axioms resolutionDerivedExtensionIso_self
#print axioms resolutionDerivedExtensionIso_trans
#print axioms derivedExtensionResolutionComputation
#print axioms derivedExtensionComparison
#print axioms derivedExtensionComparison_isIso
#print axioms restriction_quasiIso
#print axioms derivedRestriction
#print axioms derivedRestriction_fac
#print axioms extension_quasiIso_of_flat
#print axioms moduleExtension_quasiIso_of_flat
#print axioms derivedExtensionComparison_isIso_of_flat
end SerrePositivity.DifferentialGraded.ScalarExtension
