module
public import SerrePositivity.DifferentialGraded.Derived.TensorResolutionComparison
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 導来tensorの両変数選択独立性と任意解像度比較 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctor A D R ≅ moduleResolutionDerivedTensorBifunctor A D S :=
  moduleResolutionDerivedTensorBifunctorIso A D R S

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) {M : ModuleCategory A D}
    (P Q : ModuleProjectiveResolution A D M) :
    moduleTensorBifunctorResolutionComputation A D R L P ≪≫
        moduleProjectiveResolutionTensorIso A D P Q (ForgetEnrichment.to (Complex A) L) =
      moduleTensorBifunctorResolutionComputation A D R L Q :=
  moduleTensorBifunctorResolutionComputation_trans A D R L P Q

example [HasDerivedCategory.{w} (ModuleCat.{0} (ZMod 2))]
    {M : ModuleCategory (ZMod 2) PUnit.{1}}
    (P Q : ModuleProjectiveResolution (ZMod 2) PUnit.{1} M) :
    moduleProjectiveResolutionTensorLeftFunctor (ZMod 2) PUnit.{1} P ≅
      moduleProjectiveResolutionTensorLeftFunctor (ZMod 2) PUnit.{1} Q :=
  moduleProjectiveResolutionTensorLeftIso (ZMod 2) PUnit.{1} P Q

#print axioms moduleResolutionDerivedTensorLeftIso
#print axioms moduleResolutionDerivedTensorLeftIso_hom_app
#print axioms moduleResolutionDerivedTensorLeftIso_self
#print axioms moduleResolutionDerivedTensorLeftIso_trans
#print axioms moduleResolutionDerivedTensorBifunctorFacIso
#print axioms moduleResolutionDerivedTensorBifunctor_lifting
#print axioms moduleResolutionDerivedTensorBifunctorIso
#print axioms moduleResolutionDerivedTensorBifunctorIso_hom_app
#print axioms moduleResolutionDerivedTensorBifunctorIso_self
#print axioms moduleResolutionDerivedTensorBifunctorIso_trans
#print axioms moduleProjectiveResolutionTensorLeftFunctor
#print axioms moduleProjectiveResolutionTensorLeftIso
#print axioms moduleProjectiveResolutionTensorLeftIso_self
#print axioms moduleProjectiveResolutionTensorLeftIso_trans
#print axioms moduleTensorBifunctorResolutionComputation
#print axioms moduleTensorBifunctorResolutionComputation_trans
