module
public import SerrePositivity.DifferentialGraded.Derived.HomBifunctor

/-! # U10b7f：両変数の指定局所化上の全導来Hom -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example : (DerivedModuleCategory A D)ᵒᵖ ⥤
    (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) := moduleDerivedHomBifunctor A D

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M N : ModuleCategory A D) :
    ((moduleResolutionDerivedHomBifunctor A D R).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅ DerivedCategory.Q.obj ((R M).obj ⟶[Complex A] N) :=
  moduleResolutionDerivedHomBifunctorComputation A D R M N

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleToDerived A D).op ⋙ moduleResolutionDerivedHomBifunctor A D R ≅
      moduleResolutionHomSourceFunctor A D R := moduleResolutionDerivedHomBifunctor_fac A D R

example {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M)
    (N : ModuleCategory A D) :
    ((moduleDerivedHomBifunctor A D).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅ DerivedCategory.Q.obj (P.obj ⟶[Complex A] N) :=
  moduleDerivedHomBifunctorResolutionComputation A D P N

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleResolutionHomSourceFunctor
#print axioms moduleResolutionHomSourceFunctor_inverts
#print axioms moduleResolutionDerivedHomBifunctor
#print axioms moduleResolutionDerivedHomBifunctor_lifting
#print axioms moduleResolutionDerivedHomBifunctor_fac
#print axioms moduleResolutionDerivedHomBifunctorComputation
#print axioms moduleDerivedHomBifunctor
#print axioms moduleDerivedHomBifunctorResolutionComputation
