module
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # U10b7a：射影的始域からの導来Hom関手と計算同型 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example (T : ModuleCategory A D) (hT : moduleHomotopicallyProjective A D T) :
    moduleToDerived A D ⋙ moduleDerivedHomOut A D T hT = moduleHomOutToDerived A D T :=
  moduleDerivedHomOut_fac A D T hT

example (T : ModuleCategory A D) (hT : moduleHomotopicallyProjective A D T)
    (N : ModuleCategory A D) :
    (moduleDerivedHomOut A D T hT).obj ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj (moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N)) := moduleDerivedHomOutComputation A D T hT N

example (M : ModuleCategory A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) := moduleResolvedHomOut A D M

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleHomOutToDerived
#print axioms moduleHomOutToDerived_inverts
#print axioms moduleDerivedHomOut
#print axioms moduleDerivedHomOut_fac
#print axioms moduleDerivedHomOutComputation
#print axioms moduleResolvedHomOut
