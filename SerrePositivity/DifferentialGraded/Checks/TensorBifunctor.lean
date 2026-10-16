module
public import SerrePositivity.DifferentialGraded.Derived.TensorBifunctor
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 両変数導来tensorと任意解像度計算の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example : DerivedLeftModuleCategory A D ⥤
    (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  moduleDerivedTensorBifunctor A D

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorBifunctor A D R).obj
      ((leftModuleToDerived A D).obj L)).obj ((moduleToDerived A D).obj M) ≅
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D
      (ForgetEnrichment.to (Complex A) L)).obj (R M).obj) :=
  moduleResolutionDerivedTensorBifunctorComputation A D R L M

example [HasDerivedCategory.{w} (ModuleCat.{0} (ZMod 2))] :
    DerivedLeftModuleCategory (ZMod 2) PUnit.{1} ⥤
      (DerivedModuleCategory (ZMod 2) PUnit.{1} ⥤ DerivedCategory (ModuleCat.{0} (ZMod 2))) :=
  moduleDerivedTensorBifunctor (ZMod 2) PUnit.{1}

#print axioms DerivedLeftModuleCategory
#print axioms leftModuleToDerived
#print axioms leftModuleToDerived_inverts
#print axioms leftModuleDerivedIso
#print axioms moduleProjectiveTensorLeftMap_isIso
#print axioms moduleResolutionDerivedTensorLeftFunctor_inverts
#print axioms moduleDerivedTensorLeftFunctor_inverts
#print axioms moduleResolutionDerivedTensorBifunctor
#print axioms moduleResolutionDerivedTensorBifunctor_fac
#print axioms moduleDerivedTensorBifunctor
#print axioms moduleDerivedTensorBifunctor_fac
#print axioms moduleResolutionDerivedTensorBifunctor_obj
#print axioms moduleResolutionDerivedTensorBifunctorComputation
