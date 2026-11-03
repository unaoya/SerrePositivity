module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10b3c：余積のHom endとhomotopically projective性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {J : Type w} [Small.{u} J] (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M)) (ForgetEnrichment.to (Complex A) N) ≅
      ∏ᶜ moduleCoproductHomFamily A D M N := moduleCoproductHomIso A D M N
example {J : Type w} [Small.{u} J] (M : J → ModuleCategory A D) (N : ModuleCategory A D) (j : J) :
    (moduleCoproductHomIso A D M N).hom ≫ Pi.π (moduleCoproductHomFamily A D M N) j =
      eHomWhiskerRight (Complex A) (Sigma.ι M j) N := moduleCoproductHomIso_hom_π A D M N j
example {J : Type w} [Small.{u} J] (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    moduleHomotopicallyProjective A D (∐ M) := moduleCoproduct_homotopicallyProjective A D M hM
example {M : ModuleCategory A D} (S : ModuleSphereFreePresentation A D M) :
    moduleHomotopicallyProjective A D M := S.homotopicallyProjective A D
example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.quotient n) := F.quotient_homotopicallyProjective A D n
example {K : Complex A} {M N : ModuleCategory A D} (f : moduleTensorLeftObj A D K M ⟶ N) :
    moduleParamUncurry A D (moduleParamCurry A D f) = f := moduleParamUncurry_curry A D f
example : moduleHomotopicallyProjective ℤ PUnit.{1}
    (∐ fun n : ℕ => freeSphere ℤ PUnit.{1} PUnit.unit (n : ℤ)) :=
  moduleCoproduct_homotopicallyProjective ℤ PUnit.{1} _
    (fun n => freeSphere_homotopicallyProjective ℤ PUnit.{1} PUnit.unit (n : ℤ))
example : moduleHomotopicallyProjective (ZMod 2) PUnit.{1}
    (∐ fun n : ℕ => freeSphere (ZMod 2) PUnit.{1} PUnit.unit (-(n : ℤ))) :=
  moduleCoproduct_homotopicallyProjective (ZMod 2) PUnit.{1} _
    (fun n => freeSphere_homotopicallyProjective (ZMod 2) PUnit.{1} PUnit.unit (-(n : ℤ)))
end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded

#print axioms moduleParamCurry
#print axioms moduleParamCurry_π
#print axioms moduleParamUncurry_curry
#print axioms moduleParamCurry_uncurry
#print axioms moduleParamUncurry_injective
#print axioms moduleParamUncurry_naturality_source
#print axioms moduleCoproductHomFamily
#print axioms moduleCoproductHomFan
#print axioms moduleCoproductHomLift
#print axioms moduleCoproductHomLift_π
#print axioms moduleCoproductHomIsLimit
#print axioms moduleCoproductHomIso
#print axioms moduleCoproductHomIso_hom_π
#print axioms moduleCoproduct_homotopicallyProjective
#print axioms ModuleSphereFreePresentation.homotopicallyProjective
#print axioms ModuleSemifreeFiltration.initial_homotopicallyProjective
#print axioms ModuleSemifreeFiltration.quotient_homotopicallyProjective
