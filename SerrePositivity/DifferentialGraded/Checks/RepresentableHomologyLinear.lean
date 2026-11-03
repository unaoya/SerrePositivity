module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.Basic

public import Mathlib.Data.ZMod.Basic

/-! # 導来Hom計算の線形性とcycle類の自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : Linear A (DerivedModuleCategory A D) := inferInstance
example : (moduleToDerived A D).Linear A := inferInstance
example (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃ₗ[A]
      (moduleDerivedHomology A D x 0).obj X := moduleRepresentableDerivedHomLinearEquiv A D x X

example (x : D) (X : DerivedModuleCategory A D) (a : A)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomEquiv A D x X (a • f) =
      a • moduleRepresentableDerivedHomEquiv A D x X f := by
  rw [← moduleRepresentableDerivedHomLinearEquiv_toEquiv]
  exact (moduleRepresentableDerivedHomLinearEquiv A D x X).map_smul a f

example {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) :
    homologyMap f 0 (complexZeroHomologyClass A K c) =
      complexZeroHomologyClass A L (complexMapZeroCycle A f c) :=
  complexZeroHomologyClass_naturality A f c

example : Linear (ZMod 2) (DerivedModuleCategory (ZMod 2) PUnit.{1}) := inferInstance

#print axioms complexZeroHomologyClass_add
#print axioms complexZeroHomologyClass_smul
#print axioms closedHomEquiv_add
#print axioms closedHomEquiv_smul
#print axioms homotopyHomologyEquiv_add
#print axioms homotopyHomologyEquiv_smul
#print axioms homotopyHomologyLinearEquiv
#print axioms complexZeroCycle
#print axioms complexZeroCycle_iCycles
#print axioms complexZeroHomologyClass_eq
#print axioms complexMapZeroCycle
#print axioms complexZeroCycle_map
#print axioms complexZeroHomologyClass_naturality
#print axioms closedHomEquiv_postcompose
#print axioms homotopyHomologyEquiv_postcompose
#print axioms moduleToDerivedAdditive
#print axioms moduleProjectiveDerivedHomEquiv_add
#print axioms moduleProjectiveDerivedHomEquiv_smul
#print axioms moduleProjectiveDerivedHomLinearEquiv
#print axioms moduleProjectiveDerivedHomologyLinearEquiv
#print axioms moduleRepresentableDerivedHomologyLinearEquiv
#print axioms moduleRepresentableDerivedHomLinearEquiv
#print axioms moduleRepresentableDerivedHomLinearEquiv_toEquiv
