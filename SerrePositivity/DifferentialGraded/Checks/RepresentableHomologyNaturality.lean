module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 代表加群のHom計算の全導来射に対する自然性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (x : D) {X Y : DerivedModuleCategory A D} (g : X ⟶ Y)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomLinearEquiv A D x Y (f ≫ g) =
      (moduleDerivedHomology A D x 0).map g
        (moduleRepresentableDerivedHomLinearEquiv A D x X f) :=
  moduleRepresentableDerivedHomLinearEquiv_naturality A D x g f

example (x : D) {M N : ModuleCategory A D} (w : M ⟶ N) (hw : moduleQuasiIso A D w)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    letI := moduleToDerived_inverts A D w hw
    moduleRepresentableDerivedHomEquiv A D x ((moduleToDerived A D).obj M)
        (f ≫ inv ((moduleToDerived A D).map w)) =
      (moduleDerivedHomology A D x 0).map (inv ((moduleToDerived A D).map w))
        (moduleRepresentableDerivedHomEquiv A D x ((moduleToDerived A D).obj N) f) := by
  exact moduleRepresentableDerivedHomEquiv_naturality A D x _ f

example (x : D) : moduleRepresentableDerivedCoyoneda A D x ≅ moduleDerivedHomologyLift A D x :=
  moduleRepresentableHomologyNatIso A D x

example : moduleRepresentableDerivedCoyoneda (ZMod 2) PUnit.{1} PUnit.unit ≅
    moduleDerivedHomologyLift (ZMod 2) PUnit.{1} PUnit.unit :=
  moduleRepresentableHomologyNatIso (ZMod 2) PUnit.{1} PUnit.unit

#print axioms moduleProjectiveDerivedHomologyEquiv_postcompose
#print axioms dgYonedaIso_postcompose
#print axioms moduleRepresentableDerivedHomologyEquiv_postcompose
#print axioms moduleRepresentableDerivedCoyoneda
#print axioms moduleDerivedHomologyLift
#print axioms moduleRepresentableHomologyPreNatIso
#print axioms moduleRepresentableHomologyNatIso
#print axioms moduleRepresentableHomologyNatIso_app_obj
#print axioms moduleRepresentableHomologyNatIso_app
#print axioms moduleRepresentableDerivedHomEquiv_naturality
#print axioms moduleRepresentableDerivedHomLinearEquiv_naturality
