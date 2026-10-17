module
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionPaths
public import Mathlib.Data.ZMod.Basic

@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
open SerrePositivity.DifferentialGraded.ScalarExtension
example (S : Set PUnit.{1}) (w : Word S) (x y : PUnit.{1}) :
    IsIso (termBaseChangeIso (Int.castRingHom (ZMod 2)) PUnit.{1} w x y).hom := inferInstance

#print axioms termBaseChangeIso
#print axioms termBaseChangeIso_cons_hom
#print axioms internalHomBaseChangeIso
#print axioms map_ι_internalHomBaseChangeIso
#print axioms map_originalHom_internalHomBaseChangeIso
end SerrePositivity.DifferentialGraded.DGQuotient
