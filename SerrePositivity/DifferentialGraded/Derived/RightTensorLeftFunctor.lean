module
public import SerrePositivity.DifferentialGraded.Derived.RightTensor
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-! # 左加群の閉零圏に関する導来tensorの関手性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 左加群の射を、右変数を導来化したtensor関手間の自然変換へ送る。 -/
def moduleResolutionDerivedTensorLeftFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    LeftModuleCategory A D ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  BalancedTensor.rightTensorHomotopyBifunctor A D ⋙
    (Functor.whiskeringLeft (DerivedModuleCategory A D) (ModuleHomotopyCategory A D)
      (_root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ))).obj
        (moduleDerivedResolutionFunctor A D R) ⋙
    (Functor.whiskeringRight (DerivedModuleCategory A D)
      (_root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) (DerivedCategory (ModuleCat.{u} A))).obj
        DerivedCategory.Qh

lemma moduleResolutionDerivedTensorLeftFunctor_obj
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorLeftFunctor A D R).obj L =
      moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L) := rfl

lemma moduleResolutionDerivedTensorLeftFunctor_map_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {L L' : LeftModuleCategory A D} (g : L ⟶ L') (X : DerivedModuleCategory A D) :
    ((moduleResolutionDerivedTensorLeftFunctor A D R).map g).app X =
      DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D g).app
        ((moduleDerivedResolutionFunctor A D R).obj X)) := rfl

/-- 標準解像度を用いた導来tensorは左加群の通常射に関して関手的。 -/
def moduleDerivedTensorLeftFunctor :
    LeftModuleCategory A D ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  moduleResolutionDerivedTensorLeftFunctor A D (moduleCanonicalProjectiveResolution A D)

lemma moduleDerivedTensorLeftFunctor_obj (L : LeftModuleCategory A D) :
    (moduleDerivedTensorLeftFunctor A D).obj L =
      moduleDerivedTensorRight A D (ForgetEnrichment.to (Complex A) L) := rfl

end SerrePositivity.DifferentialGraded
