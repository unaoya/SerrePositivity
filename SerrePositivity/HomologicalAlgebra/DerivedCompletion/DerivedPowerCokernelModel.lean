module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelTensorModel
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor

/-! # Ordinary power cokernels compute actual derived reduction in projective models -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- The standard quotient's original R-action agrees with restriction along
the actual quotient homomorphism. -/
def powerQuotientCoefficientIso (n : ℕ) :
    ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) ≅
      baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a ^ n})) :=
  (LinearEquiv.refl R (R ⧸ Ideal.span {a ^ n})).toModuleIso

/-- Actual derived reduction, restricted to R, is the ordinary cokernel of
a^n on the chosen projective model, without any regularity assumption. -/
def derivedPowerCokernelModelIso (n : ℕ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X)).obj ≅
        DerivedCategory.Q.obj
          (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n) :=
  restrictedDerivedBaseChangeModelIso (Ideal.Quotient.mk (Ideal.span {a ^ n})) X ≪≫
    DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso
      (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a ^ n})))
      (boundedAboveDerivedChosenModel X).complex) ≪≫
    DerivedCategory.Q.mapIso ((moduleTensorCochainFunctor
      (boundedAboveDerivedChosenModel X).complex).mapIso (powerQuotientCoefficientIso a n).symm) ≪≫
    DerivedCategory.Q.mapIso (powerCokernelTensorModelIso a
      (boundedAboveDerivedChosenModel X).complex (fun i ↦ by
        have : Module.Projective R ((boundedAboveDerivedChosenModel X).complex.X i) := inferInstance
        infer_instance) n).symm

/-- Homology of the actual power reduction is computed by the same cokernel model
in every degree, with its original restricted coefficient action. -/
def derivedPowerCokernelHomologyIso (n : ℕ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) :
    (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) i).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (derivedPowerCokernelModelIso a n X).symm ≪≫
    (derivedRestrictScalarsHomologyIso (Ideal.Quotient.mk (Ideal.span {a ^ n})) i).app _

lemma powerCokernel_homology_isZero_of_reduction (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj)) :
    IsZero ((powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i) :=
  (derivedPowerCokernelHomologyIso a n X i).isZero_iff.mpr
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).map_isZero h)

end SerrePositivity.DerivedCompletion
