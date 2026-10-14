module
public import SerrePositivity.HomologicalAlgebra.PrincipalQuotientResolution
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.PerfectComplex.TensorCone

/-! # A regular principal derived quotient is the two-term Koszul reduction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Tensoring scalar multiplication on the unit identifies it with scalar multiplication. -/
lemma cochainTensorUnitScalar_leftUnitor (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap (smulId a (cochainTensorUnit (R := R))) (𝟙 P) ≫
        (cochainTensorLeftUnitor P).hom =
      (cochainTensorLeftUnitor P).hom ≫ smulId a P := by
  rw [smulId, cochainTensorMap_smul_left, cochainTensorMap_id]
  simp [smulId, Linear.smul_comp, Linear.comp_smul]

/-- Tensoring the unit scalar cone with any complex gives its scalar cone. -/
def cochainTensorUnitScalarConeIso (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R)))) P ≅
      (scalarConeFunctor a).obj P :=
  cochainTensorConeLeft (smulId a (cochainTensorUnit (R := R))) P ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk (cochainTensorLeftUnitor P) (cochainTensorLeftUnitor P)
        (cochainTensorUnitScalar_leftUnitor a P).symm)

/-- The actual derived tensor with a regular quotient computes the derived Koszul cone. -/
def boundedAboveDerivedTensorQuotientKoszulIso (a : R) (ha : IsSMulRegular R a)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedTensor.obj
        (derivedBaseChangeScalarObject (Ideal.Quotient.mk (Ideal.span {a})), X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor R a).obj X.obj :=
  boundedAboveDerivedTensorModelIso _ _ (principalQuotientDerivedModel a ha)
      (boundedAboveDerivedChosenModel X) ≪≫
    DerivedCategory.Q.mapIso (cochainTensorUnitScalarConeIso a
      (boundedAboveDerivedChosenModel X).complex) ≪≫
    (DerivedCompletion.derivedScalarConeComparison R a).symm.app
      (boundedAboveDerivedChosenModel X).complex ≪≫
    (DerivedCompletion.derivedScalarConeFunctor R a).mapIso
      (boundedAboveDerivedChosenModel X).iso

/-- In particular, actual scalar extension to R/(a), restricted to R, is Koszul reduction. -/
def restrictedDerivedQuotientKoszulIso (a : R) (ha : IsSMulRegular R a)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor R a).obj X.obj :=
  DerivedCategory.Minus.ι.mapIso
      (boundedAboveDerivedBaseChangeTensorIso (Ideal.Quotient.mk (Ideal.span {a})) X) ≪≫
    boundedAboveDerivedTensorQuotientKoszulIso a ha X

end SerrePositivity
