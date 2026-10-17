module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import Mathlib.Data.ZMod.Basic

/-! # graph導来延長–制限随伴・自然性・三角恒等式の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 任意可換環・独立宇宙。元のHomのflatness・有界性は要求しない。
example : dgDerivedExtension A D E F ⊣ dgDerivedRestriction A D E F :=
  dgDerivedExtensionRestrictionAdjunction A D E F

example {X X' : DerivedModuleCategory A D} (f : X ⟶ X') (Y : DerivedModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj X' ⟶ Y) :
    dgDerivedExtensionHomEquiv A D E F X Y ((dgDerivedExtension A D E F).map f ≫ φ) =
      f ≫ dgDerivedExtensionHomEquiv A D E F X' Y φ :=
  dgDerivedExtensionHomEquiv_naturality_left A D E F f Y φ

example (X : DerivedModuleCategory A D) {Y Y' : DerivedModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj X ⟶ Y) (g : Y ⟶ Y') :
    dgDerivedExtensionHomEquiv A D E F X Y' (φ ≫ g) =
      dgDerivedExtensionHomEquiv A D E F X Y φ ≫ (dgDerivedRestriction A D E F).map g :=
  dgDerivedExtensionHomEquiv_naturality_right A D E F X φ g

example (X : DerivedModuleCategory A D) :
    (dgDerivedExtension A D E F).map ((dgDerivedExtensionUnit A D E F).app X) ≫
      (dgDerivedExtensionCounit A D E F).app ((dgDerivedExtension A D E F).obj X) = 𝟙 _ :=
  dgDerivedExtension_left_triangle A D E F X

example (Y : DerivedModuleCategory A E) :
    (dgDerivedExtensionUnit A D E F).app ((dgDerivedRestriction A D E F).obj Y) ≫
      (dgDerivedRestriction A D E F).map ((dgDerivedExtensionCounit A D E F).app Y) = 𝟙 _ :=
  dgDerivedExtension_right_triangle A D E F Y

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) :
    dgDerivedExtension (ZMod 2) X Y F ⊣ dgDerivedRestriction (ZMod 2) X Y F :=
  dgDerivedExtensionRestrictionAdjunction (ZMod 2) X Y F

namespace SerrePositivity.DifferentialGraded
#print axioms DGFunctor.homotopyAdjunction_homEquiv_map
#print axioms dgProjectiveDerivedExtensionHomEquiv_map
#print axioms dgDerivedRestrictionComputation_inv_naturality
#print axioms dgProjectiveDerivedExtensionHomEquiv_naturality_right
#print axioms dgProjectiveDerivedExtensionHomEquiv_naturality_left
#print axioms dgExtensionHomotopyComputation_naturality
#print axioms dgResolutionDerivedExtensionComputation_naturality
#print axioms dgDerivedExtensionResolutionComputation_canonical
#print axioms dgDerivedExtensionResolutionComputation_inv_naturality
#print axioms dgDerivedExtensionHomEquivOnModules_apply
#print axioms dgDerivedExtensionHomEquivOnModules_naturality_right
#print axioms dgResolutionLift_derived_fac
#print axioms dgResolutionLift_derived_inv_naturality
#print axioms dgDerivedExtensionHomEquivOnModules_naturality_left
#print axioms dgDerivedExtensionHomEquiv_naturality_right
#print axioms dgDerivedExtensionHomEquiv_naturality_left
#print axioms dgDerivedExtensionRestrictionAdjunction
#print axioms dgDerivedExtensionUnit
#print axioms dgDerivedExtensionCounit
#print axioms dgDerivedExtension_left_triangle
#print axioms dgDerivedExtension_right_triangle
end SerrePositivity.DifferentialGraded
