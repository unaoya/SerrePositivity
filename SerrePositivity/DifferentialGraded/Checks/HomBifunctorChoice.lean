module
public import SerrePositivity.DifferentialGraded.Derived.HomBifunctorChoice

/-! # U10b7g：導来Hom双関手の解像度族選択独立性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedHomBifunctor A D ≅ moduleResolutionDerivedHomBifunctor A D R :=
  moduleDerivedHomBifunctorChoiceIso A D R

example (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R S ≪≫
      moduleResolutionDerivedHomBifunctorIso A D S T =
        moduleResolutionDerivedHomBifunctorIso A D R T :=
  moduleResolutionDerivedHomBifunctorIso_trans A D R S T

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R R = Iso.refl _ :=
  moduleResolutionDerivedHomBifunctorIso_self A D R

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleResolutionHomSourceIso
#print axioms moduleResolutionHomSourceIso_app
#print axioms moduleResolutionHomSourceIso_self
#print axioms moduleResolutionHomSourceIso_trans
#print axioms moduleResolutionDerivedHomBifunctorIso
#print axioms moduleResolutionDerivedHomBifunctorIso_app
#print axioms moduleResolutionDerivedHomBifunctorIso_self
#print axioms moduleResolutionDerivedHomBifunctorIso_trans
#print axioms moduleDerivedHomBifunctorChoiceIso
