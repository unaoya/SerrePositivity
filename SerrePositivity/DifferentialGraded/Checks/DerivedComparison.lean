module
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison

/-! # U9b2：境界を同一視する局所化と閉零/K(D)局所化比較 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : DerivedModuleCategory A D ≌ HomotopyDerivedModuleCategory A D :=
  moduleDerivedHomotopyEquivalence A D
example : (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D).IsLocalization
    (moduleQuasiIso A D) := inferInstance
example : (moduleHomotopyToDerivedClosed A D).IsLocalization (moduleHomotopyQuasiIso A D) :=
  inferInstance
example : moduleToDerived A D ⋙ (moduleDerivedHomotopyEquivalence A D).functor ≅
    moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D := moduleDerivedHomotopyComparisonIso A D
example : moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D ≅ moduleToDerived A D :=
  moduleToHomotopyDerivedIso A D
example : (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) ⋙
    (moduleDerivedHomotopyEquivalence A D).inverse ≅ moduleToDerived A D :=
  moduleDerivedHomotopyInverseComparisonIso A D
variable {E : Type w} [Category.{w'} E]
example (F : ModuleCategory A D ⥤ E) (hF : (moduleQuasiIso A D).IsInvertedBy F)
    {M N : ModuleCategory A D} (f g : M ⟶ N) (h : ModuleHomotopy A D f g) :
    F.map f = F.map g :=
  moduleQuasiIso_equalizes_boundary A D F hF f g
    ((moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩)
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_equalizes_boundary
#print axioms SerrePositivity.DifferentialGraded.moduleBoundaryFactorsThroughLocalization
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyCompositeIsLocalization
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedHomotopyEquivalence
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedHomotopyComparisonIso
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedHomotopyInverseComparisonIso
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosedIsLocalization
#print axioms SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso
