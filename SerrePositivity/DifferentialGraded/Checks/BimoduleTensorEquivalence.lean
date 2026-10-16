module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFull
public import Mathlib.Data.ZMod.Basic

/-! # 積dg圏上の加群と主bimodule圏の閉零圏同値の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

example : (BimoduleTensorModule.functor A B C).Full := inferInstance
example : (BimoduleTensorModule.functor A B C).IsEquivalence := inferInstance
example : BimoduleTensorModuleCategory A B C ≌ BimoduleCategory A B C :=
  BimoduleTensorModule.equivalence A B C

example {M N : BimoduleTensorModuleCategory A B C}
    (a : (BimoduleTensorModule.functor A B C).obj M ⟶
      (BimoduleTensorModule.functor A B C).obj N) :
    (BimoduleTensorModule.functor A B C).map
      (BimoduleTensorModule.preimageMap A B C a) = a :=
  BimoduleTensorModule.map_preimageMap A B C a

example {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleTensorModule.preimageMap A B C
      ((BimoduleTensorModule.functor A B C).map f) = f :=
  BimoduleTensorModule.preimageMap_map A B C f

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] :
    BimoduleTensorModuleCategory (ZMod 2) B C ≌ BimoduleCategory (ZMod 2) B C :=
  BimoduleTensorModule.equivalence (ZMod 2) B C

#print axioms BimoduleCategory.valueMap_uncurry_naturality
#print axioms BimoduleTensorModule.preimage_naturality
#print axioms BimoduleTensorModule.preimageMap
#print axioms BimoduleTensorModule.preimageMap_eval
#print axioms BimoduleTensorModule.map_preimageMap
#print axioms BimoduleTensorModule.preimageMap_map
#print axioms BimoduleTensorModule.preimageMap_quasiIso_iff
#print axioms BimoduleTensorModule.full
#print axioms BimoduleTensorModule.isEquivalence
#print axioms BimoduleTensorModule.equivalence
