module
public import SerrePositivity.DifferentialGraded.StageSeven

/-! # U0–U10 の統合受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleCanonicalProjectiveResolution A D M).π :=
  (moduleCanonicalProjectiveResolution A D M).quasiIso
example (M : ModuleCategory A D) :
    moduleHomotopicallyProjective A D (moduleCanonicalProjectiveResolution A D M).obj :=
  (moduleCanonicalProjectiveResolution A D M).projective
example (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  exists_semifree_resolution A D M
example : IsTriangulated (ModuleHomotopyCategory A D) := inferInstance
example : IsTriangulated (DerivedModuleCategory A D) := inferInstance
example : LocallySmall.{u} (DerivedModuleCategory A D) := inferInstance
example (J : Type w) [Small.{u} J] :
    HasColimitsOfShape (Discrete J) (ModuleHomotopyCategory A D) := inferInstance
example (J : Type w) [Small.{u} J] :
    HasColimitsOfShape (Discrete J) (DerivedModuleCategory A D) := inferInstance
example : (moduleDerivedVerdierEquivalence A D).functor.IsTriangulated := inferInstance
example : (moduleDerivedVerdierEquivalence A D).inverse.IsTriangulated := inferInstance

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedHomBifunctor A D ≅ moduleResolutionDerivedHomBifunctor A D R :=
  moduleDerivedHomBifunctorChoiceIso A D R
example : (ringDerivedEquivalence A).functor.IsTriangulated := inferInstance
example : (ringDerivedEquivalence A).inverse.IsTriangulated := inferInstance

#print axioms exists_semifree_resolution
#print axioms moduleSemifree_homotopicallyProjective
#print axioms moduleDerivedHomBifunctorChoiceIso
#print axioms moduleResolutionDerivedHomEquiv
#print axioms moduleDerivedLocallySmall
#print axioms moduleDerivedHasCoproductsOfShape
#print axioms moduleHomotopyIsTriangulated
#print axioms moduleDerivedIsTriangulated
#print axioms moduleDerivedVerdierEquivalence
#print axioms ringDerivedEquivalenceIsTriangulated
#print axioms ringDerivedEquivalencePreservesCoproducts
