module
public import SerrePositivity.DifferentialGraded.Derived.LeftBasic
public import SerrePositivity.DifferentialGraded.Derived.LeftTensorInversion

/-! # 両変数を指定局所化した導来balanced tensor -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 射影解像度族を指定した、左右の導来加群圏上のtensor双関手。 -/
def moduleResolutionDerivedTensorBifunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedLeftModuleCategory A D ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  Localization.Construction.lift (moduleResolutionDerivedTensorLeftFunctor A D R)
    (moduleResolutionDerivedTensorLeftFunctor_inverts A D R)

lemma moduleResolutionDerivedTensorBifunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    leftModuleToDerived A D ⋙ moduleResolutionDerivedTensorBifunctor A D R =
      moduleResolutionDerivedTensorLeftFunctor A D R :=
  Localization.Construction.fac _ _

/-- 標準semifree解像度による両変数導来tensor。 -/
def moduleDerivedTensorBifunctor : DerivedLeftModuleCategory A D ⥤
    (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  moduleResolutionDerivedTensorBifunctor A D (moduleCanonicalProjectiveResolution A D)

lemma moduleDerivedTensorBifunctor_fac :
    leftModuleToDerived A D ⋙ moduleDerivedTensorBifunctor A D =
      moduleDerivedTensorLeftFunctor A D :=
  moduleResolutionDerivedTensorBifunctor_fac A D (moduleCanonicalProjectiveResolution A D)

/-- 左変数の局所化前で、既存の右変数導来tensorと厳密に一致する。 -/
lemma moduleResolutionDerivedTensorBifunctor_obj
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorBifunctor A D R).obj ((leftModuleToDerived A D).obj L) =
      moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L) :=
  congrArg (fun F => F.obj L) (moduleResolutionDerivedTensorBifunctor_fac A D R)

/-- 任意の右射影解像度族を用いた、両局所化からの具体的tensor計算。 -/
def moduleResolutionDerivedTensorBifunctorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorBifunctor A D R).obj
      ((leftModuleToDerived A D).obj L)).obj ((moduleToDerived A D).obj M) ≅
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D
      (ForgetEnrichment.to (Complex A) L)).obj (R M).obj) :=
  (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D R L)).app
    ((moduleToDerived A D).obj M) ≪≫
      moduleResolutionDerivedTensorComputation A D R (ForgetEnrichment.to (Complex A) L) M

end SerrePositivity.DifferentialGraded
