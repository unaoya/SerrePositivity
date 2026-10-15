module
public import SerrePositivity.DifferentialGraded.Module.Cylinder
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U9b1：全作用を持つcylinderとホモトピーの延長 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory HomologicalComplex HomotopicalAlgebra
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule (𝟙_ (Complex A)) M) ≅
      ForgetEnrichment.of (Complex A) M := moduleTensorUnitIso A D M
example (P : Complex A) : HomotopyEquiv (dgInterval A ⊗ P) ((𝟙_ (Complex A)) ⊗ P) :=
  tensorIntervalHomotopyEquiv A P
example (M : ModuleCategory A D) : moduleQuasiIso A D (modulePrecylinder A D M).π :=
  modulePrecylinder_π_quasiIso A D M
example {M N : ModuleCategory A D} (f g : M ⟶ N) (h : ModuleHomotopy A D f g) :
    (modulePrecylinder A D M).LeftHomotopy f g :=
  moduleCylinderLeftHomotopy A D f g ((moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩)
example {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₀ ≫ moduleCylinderDesc A D f g h = f :=
  moduleCylinderDesc_i₀ A D f g h
example {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₁ ≫ moduleCylinderDesc A D f g h = g :=
  moduleCylinderDesc_i₁ A D f g h
example (M : ModuleCategory ℤ PUnit.{1}) :
    moduleQuasiIso ℤ PUnit.{1} (modulePrecylinder ℤ PUnit.{1} M).π :=
  modulePrecylinder_π_quasiIso ℤ PUnit.{1} M
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    moduleQuasiIso (ZMod 2) PUnit.{1} (modulePrecylinder (ZMod 2) PUnit.{1} M).π :=
  modulePrecylinder_π_quasiIso (ZMod 2) PUnit.{1} M
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.uncurryRight_identity
#print axioms SerrePositivity.DifferentialGraded.uncurryRight_closedMap
#print axioms SerrePositivity.DifferentialGraded.moduleTensorUnitIso
#print axioms SerrePositivity.DifferentialGraded.moduleTensorUnitIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleTensorUnitIso_inv_eval
#print axioms SerrePositivity.DifferentialGraded.moduleParamUncurry
#print axioms SerrePositivity.DifferentialGraded.moduleParamUncurry_eval
#print axioms SerrePositivity.DifferentialGraded.moduleParamUncurry_precomp
#print axioms SerrePositivity.DifferentialGraded.moduleParamUncurry_closed
#print axioms SerrePositivity.DifferentialGraded.dgInterval
#print axioms SerrePositivity.DifferentialGraded.tensorIntervalHomotopyEquiv
#print axioms SerrePositivity.DifferentialGraded.tensorIntervalProjection_quasiIso
#print axioms SerrePositivity.DifferentialGraded.modulePrecylinder
#print axioms SerrePositivity.DifferentialGraded.modulePrecylinder_π_quasiIso
#print axioms SerrePositivity.DifferentialGraded.moduleCylinderDesc
#print axioms SerrePositivity.DifferentialGraded.moduleCylinderDesc_i₀
#print axioms SerrePositivity.DifferentialGraded.moduleCylinderDesc_i₁
#print axioms SerrePositivity.DifferentialGraded.moduleCylinderLeftHomotopy
