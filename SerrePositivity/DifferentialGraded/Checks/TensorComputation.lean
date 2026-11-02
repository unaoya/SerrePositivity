module
public import SerrePositivity.DifferentialGraded.Derived.Tensor
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 導来tensor計算と解像度族比較の統合検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    ((moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L)).app ((moduleToDerived A D).obj M) ≫
        (moduleTensorBifunctorResolutionComputation A D S L P).hom =
      (moduleTensorBifunctorResolutionComputation A D R L P).hom :=
  moduleTensorBifunctorResolutionComputation_choice A D R S L P

example [HasDerivedCategory.{w} (ModuleCat.{0} (ZMod 2))]
    (L : LeftModule (ZMod 2) PUnit.{1}) {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    (BalancedTensor.rightTensorHomotopyFunctor (ZMod 2) PUnit.{1} L ⋙ DerivedCategory.Qh).map
        ((moduleToHomotopy (ZMod 2) PUnit.{1}).map f) ≫
          (moduleTensorDerivedHomotopyComputation (ZMod 2) PUnit.{1} L N).hom =
      (moduleTensorDerivedHomotopyComputation (ZMod 2) PUnit.{1} L M).hom ≫
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor (ZMod 2) PUnit.{1} L).map f) :=
  moduleTensorDerivedHomotopyComputation_naturality (ZMod 2) PUnit.{1} L f

#print axioms moduleTensorHomotopyComputation_naturality
#print axioms moduleTensorDerivedHomotopyComputation
#print axioms moduleTensorDerivedHomotopyComputation_naturality
#print axioms moduleResolutionDerivedTensorComputation_choice
#print axioms moduleResolutionDerivedTensorBifunctorIso_fac
#print axioms moduleResolutionDerivedTensorBifunctorComputation_choice
#print axioms moduleTensorBifunctorResolutionComputation_choice
