module
public import SerrePositivity.DifferentialGraded.Derived.FreeSphereProjective
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U10b2：自由sphereの全次数Homとhomotopically projective性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (K : Complex A) (n p : ℤ) :
    (homComplex A (complexSphere A n) K).X p ≃ₗ[A] K.X (n + p) :=
  complexSphereHomElementLinearEquiv A K n p
example (K : Complex A) (n p q : ℤ) (z : (homComplex A (complexSphere A n) K).X p) :
    complexSphereHomElementEquiv A K n q ((homComplex A (complexSphere A n) K).d p q z) =
      K.d (n + p) (n + q) (complexSphereHomElementEquiv A K n p z) :=
  complexSphereHomElementEquiv_d A K n p q z
example (K : Complex A) (hK : K.Acyclic) (n : ℤ) :
    (homComplex A (complexSphere A n) K).Acyclic := complexSphereHom_acyclic A K n hK
example (x : D) (n : ℤ) : moduleHomotopicallyProjective A D (freeSphere A D x n) :=
  freeSphere_homotopicallyProjective A D x n
example (x : D) (n : ℤ) (N : ModuleCategory A D) (hN : moduleAcyclic A D N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (freeSphere A D x n))
      (ForgetEnrichment.to (Complex A) N)).ExactAt (-1) :=
  freeSphere_homotopicallyProjective A D x n N hN (-1)
example : moduleHomotopicallyProjective ℤ PUnit.{1} (freeSphere ℤ PUnit.{1} PUnit.unit (-2)) :=
  freeSphere_homotopicallyProjective ℤ PUnit.{1} PUnit.unit (-2)
example : moduleHomotopicallyProjective (ZMod 2) PUnit.{1}
    (freeSphere (ZMod 2) PUnit.{1} PUnit.unit 1) :=
  freeSphere_homotopicallyProjective (ZMod 2) PUnit.{1} PUnit.unit 1
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complexSphereHomElementEquiv
#print axioms SerrePositivity.DifferentialGraded.complexSphereHomElementLinearEquiv
#print axioms SerrePositivity.DifferentialGraded.complexSphereHomElementEquiv_zero
#print axioms SerrePositivity.DifferentialGraded.complexSphereHomElementEquiv_d
#print axioms SerrePositivity.DifferentialGraded.complexSphereHom_acyclic
#print axioms SerrePositivity.DifferentialGraded.freeSphere_homotopicallyProjective
