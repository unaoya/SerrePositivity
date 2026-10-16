module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 主HomのH⁰と代表加群による導来評価の射計算 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃
      (moduleDerivedHomology A D x 0).obj X :=
  moduleRepresentableDerivedHomEquiv A D x X

example (x : D) (N : ModuleCategory A D) (z :
    ((ForgetEnrichment.to (Complex A) N).obj (Opposite.op x)).homology 0) :
    ∃ f, moduleRepresentableDerivedHomologyEquiv A D x N f = z :=
  (moduleRepresentableDerivedHomologyEquiv A D x N).surjective z

example (x : D) (N : ModuleCategory A D)
    (f g : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    moduleRepresentableDerivedHomologyEquiv A D x N f =
      moduleRepresentableDerivedHomologyEquiv A D x N g ↔ f = g :=
  (moduleRepresentableDerivedHomologyEquiv A D x N).injective.eq_iff

example (X : DerivedModuleCategory (ZMod 2) PUnit.{1}) :
    ((moduleToDerived (ZMod 2) PUnit.{1}).obj
      (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) PUnit.unit)) ⟶ X) ≃
        (moduleDerivedHomology (ZMod 2) PUnit.{1} PUnit.unit 0).obj X :=
  moduleRepresentableDerivedHomEquiv (ZMod 2) PUnit.{1} PUnit.unit X

#print axioms homotopyHomFromCycle
#print axioms homotopyHomFromCycle_surjective
#print axioms homotopyHomFromCycle_eq_iff
#print axioms homotopyHomFromCohomologyQuotient
#print axioms homotopyHomFromCohomologyQuotient_bijective
#print axioms complexZeroHomologyQuotientIso
#print axioms complexZeroHomologyClass
#print axioms homotopyHomologyEquiv
#print axioms homotopyHomologyEquiv_cycle
#print axioms homotopyHomologyEquiv_map
#print axioms moduleProjectiveDerivedHomologyEquiv
#print axioms moduleProjectiveDerivedHomologyEquiv_map
#print axioms moduleRepresentableDerivedHomologyEquiv
#print axioms moduleRepresentableDerivedHomologyEquiv_map
#print axioms moduleRepresentableDerivedHomEquiv
#print axioms moduleRepresentableDerivedHomEquiv_obj
