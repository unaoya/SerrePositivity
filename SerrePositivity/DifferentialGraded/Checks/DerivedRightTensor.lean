module
public import SerrePositivity.DifferentialGraded.Derived.RightTensorResolution
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 固定左加群との導来tensor・任意解像度計算と選択整合性 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    (moduleDerivedTensorRight A D L).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj P.obj) :=
  moduleDerivedTensorRightResolutionComputation A D P L

example (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    moduleResolutionDerivedTensorIso A D R S L ≪≫ moduleResolutionDerivedTensorIso A D S T L =
      moduleResolutionDerivedTensorIso A D R T L :=
  moduleResolutionDerivedTensorIso_trans A D R S T L

example {M : ModuleCategory A D} (P Q R : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    moduleProjectiveResolutionTensorIso A D P Q L ≪≫ moduleProjectiveResolutionTensorIso A D Q R L =
      moduleProjectiveResolutionTensorIso A D P R L :=
  moduleProjectiveResolutionTensorIso_trans A D P Q R L

section
variable [HasDerivedCategory.{w} (ModuleCat.{0} (ZMod 2))]
example (M : ModuleCategory (ZMod 2) PUnit.{1}) (L : LeftModule (ZMod 2) PUnit.{1}) :
    (moduleDerivedTensorRight (ZMod 2) PUnit.{1} L).obj
      ((moduleToDerived (ZMod 2) PUnit.{1}).obj M) ≅
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor (ZMod 2) PUnit.{1} L).obj
      (moduleCanonicalProjectiveResolution (ZMod 2) PUnit.{1} M).obj) :=
  moduleDerivedTensorRightResolutionComputation (ZMod 2) PUnit.{1}
    (moduleCanonicalProjectiveResolution (ZMod 2) PUnit.{1} M) L
end

#print axioms moduleTensorDerived_map_eq_of_homotopy_map_eq
#print axioms moduleResolutionDerivedTensor
#print axioms moduleTensorHomotopyComputation
#print axioms moduleResolutionDerivedTensorComputation
#print axioms moduleDerivedTensorRight
#print axioms moduleResolutionDerivedTensorIso
#print axioms moduleResolutionDerivedTensorIso_self
#print axioms moduleResolutionDerivedTensorIso_trans
#print axioms moduleProjectiveResolutionTensorIso
#print axioms moduleProjectiveResolutionTensorIso_hom
#print axioms moduleProjectiveResolutionTensorIso_self
#print axioms moduleProjectiveResolutionTensorIso_trans
#print axioms moduleDerivedTensorRightResolutionComputation
