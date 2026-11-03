module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import Mathlib.Data.ZMod.Basic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
open SerrePositivity.DifferentialGraded.ScalarExtension

example (S : Set PUnit.{1}) (x y : PUnit.{1}) :
    (extension (Int.castRingHom (ZMod 2))).obj (quotientHom ℤ PUnit.{1} S x y) ≅
      quotientHom (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit.{1}) S x y :=
  quotientHomBaseChangeIso (Int.castRingHom (ZMod 2)) PUnit.{1} S x y

example (S : Set PUnit.{1}) :
    DGFunctor (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) (QuotientObject PUnit.{1} S))
      (QuotientObject (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit.{1}) S) :=
  quotientBaseChangeDGFunctor (Int.castRingHom (ZMod 2)) PUnit.{1} S

#print axioms quotientHomBaseChangeIso
#print axioms quotientHomBaseChangeIso_hom_f
#print axioms originalHomInclusion_baseChange
#print axioms quotientIdentity_baseChange
#print axioms quotientComposition_baseChange
#print axioms quotientBaseChangeDGFunctor
#print axioms quotientBaseChangeDGFunctor_hom_isIso
#print axioms quotientHomBaseChangeIso_path_component
#print axioms quotientBaseChangeDGFunctor_inclusion
#print axioms ScalarExtension.derivedExtension
#print axioms ScalarExtension.derivedTensorBaseChange
end SerrePositivity.DifferentialGraded.DGQuotient
