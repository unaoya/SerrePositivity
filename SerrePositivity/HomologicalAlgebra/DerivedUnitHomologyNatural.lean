module

public import SerrePositivity.HomologicalAlgebra.UnitHomologyNaturality
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Natural linear representability of actual derived cohomology

ULift only aligns the universe of the cohomology module with that of derived Hom.
The public linear equivalence returns the original actual cohomology module.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Localization Opposite
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The module-valued functor of shifted actual maps from the unit. -/
def derivedUnitHomFunctor (n : ℤ) :
    DerivedCategory (ModuleCat.{u} R) ⥤ ModuleCat.{u + 1} R :=
  shiftFunctor _ n ⋙ (linearCoyoneda R _).obj
    (op (DerivedCategory.Q.obj (cochainTensorUnit (R := R))))

/-- The actual cochain comparison, with universes aligned, is a natural module isomorphism. -/
def unitCochainHomologyNatIso (n : ℤ) :
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n ⋙
        ModuleCat.uliftFunctor.{u + 1} R ≅
      DerivedCategory.Q ⋙ derivedUnitHomFunctor R n :=
  NatIso.ofComponents
    (fun K ↦ ((ULift.moduleEquiv : ULift.{u + 1} (K.homology n) ≃ₗ[R] K.homology n) ≪≫ₗ
      unitCochainHomologyDerivedLinearEquiv K n).toModuleIso)
    (fun f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact unitCochainHomologyDerivedLinearEquiv_naturality f n x.down)

/-- Localizing the verified cochain natural isomorphism gives naturality for all derived maps. -/
def derivedUnitHomologyNatIso (n : ℤ) :
    DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ⋙ ModuleCat.uliftFunctor.{u + 1} R ≅
      derivedUnitHomFunctor R n := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let U := ModuleCat.uliftFunctor.{u + 1} R
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n ⋙ U
  let F := derivedUnitHomFunctor R n
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
  letI : Localization.Lifting DerivedCategory.Q W HC (H ⋙ U) :=
    ⟨(Functor.associator DerivedCategory.Q H U).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors (ModuleCat R) n) U⟩
  letI : Localization.Lifting DerivedCategory.Q W (DerivedCategory.Q ⋙ F) F := ⟨Iso.refl _⟩
  exact Localization.liftNatIso DerivedCategory.Q W HC (DerivedCategory.Q ⋙ F)
    (H ⋙ U) F (unitCochainHomologyNatIso R n)

/-- The natural comparison uses the actual Hⁿ module, with its existing R-module structure. -/
def derivedUnitHomologyNaturalLinearEquiv
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj (cochainTensorUnit (R := R))) X n :=
  (ULift.moduleEquiv : ULift.{u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj X) ≃ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X).symm ≪≫ₗ
    ((derivedUnitHomologyNatIso R n).app X).toLinearEquiv

/-- This comparison commutes with every actual derived morphism, including localized inverses. -/
theorem derivedUnitHomologyNaturalLinearEquiv_naturality
    {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X) :
    derivedUnitHomologyNaturalLinearEquiv R Y n
        ((DerivedCategory.homologyFunctor (ModuleCat R) n).map f x) =
      derivedUnitHomologyNaturalLinearEquiv R X n x ≫ f⟦n⟧' := by
  exact congrArg (fun k ↦ k.hom (ULift.up x)) ((derivedUnitHomologyNatIso R n).hom.naturality f)

/-- At a represented complex the lifted comparison is the verified cochain comparison. -/
theorem derivedUnitHomologyNaturalLinearEquiv_Q
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) n).obj (DerivedCategory.Q.obj K)) :
    derivedUnitHomologyNaturalLinearEquiv R (DerivedCategory.Q.obj K) n x =
      unitCochainHomologyDerivedLinearEquiv K n
        ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).hom.app K x) := by
  change ((derivedUnitHomologyNatIso R n).hom.app (DerivedCategory.Q.obj K)).hom
    (ULift.up x) = _
  simp [derivedUnitHomologyNatIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso, unitCochainHomologyNatIso]
  rfl

/-- Actual H⁰ is naturally the ordinary Hom module from the actual unit. -/
def derivedUnitH0NaturalLinearEquiv (X : DerivedCategory (ModuleCat.{u} R)) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X ≃ₗ[R]
      (DerivedCategory.Q.obj (cochainTensorUnit (R := R)) ⟶ X) :=
  derivedUnitHomologyNaturalLinearEquiv R X 0 ≪≫ₗ
    Linear.homCongr R (Iso.refl _) ((shiftFunctorZero _ ℤ).app X)

/-- The ordinary Hom comparison commutes with every actual H⁰ map. -/
theorem derivedUnitH0NaturalLinearEquiv_naturality
    {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X) :
    derivedUnitH0NaturalLinearEquiv R Y
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f x) =
      derivedUnitH0NaturalLinearEquiv R X x ≫ f := by
  simp only [derivedUnitH0NaturalLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  rw [derivedUnitHomologyNaturalLinearEquiv_naturality]
  simp only [Category.assoc]
  erw [(shiftFunctorZero (DerivedCategory (ModuleCat R)) ℤ).hom.naturality f]
  rfl

/-- The identity of the actual unit determines its canonical H⁰ identity class. -/
def derivedUnitH0IdentityClass :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (DerivedCategory.Q.obj (cochainTensorUnit (R := R))) :=
  (derivedUnitH0NaturalLinearEquiv R _).symm (𝟙 _)

/-- The inverse comparison is exactly evaluation of the actual H⁰ map on the identity class. -/
theorem derivedUnitH0NaturalLinearEquiv_symm_apply
    (X : DerivedCategory (ModuleCat.{u} R))
    (f : DerivedCategory.Q.obj (cochainTensorUnit (R := R)) ⟶ X) :
    (derivedUnitH0NaturalLinearEquiv R X).symm f =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f (derivedUnitH0IdentityClass R) := by
  apply (derivedUnitH0NaturalLinearEquiv R X).injective
  rw [LinearEquiv.apply_symm_apply, derivedUnitH0NaturalLinearEquiv_naturality]
  change f = (derivedUnitH0NaturalLinearEquiv R
      (DerivedCategory.Q.obj (cochainTensorUnit (R := R))))
    ((derivedUnitH0NaturalLinearEquiv R
      (DerivedCategory.Q.obj (cochainTensorUnit (R := R)))).symm (𝟙 _)) ≫ f
  rw [LinearEquiv.apply_symm_apply, Category.id_comp]

end SerrePositivity
