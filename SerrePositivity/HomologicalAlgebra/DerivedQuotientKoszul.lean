module
public import SerrePositivity.HomologicalAlgebra.PrincipalQuotientResolution
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.HomologicalAlgebra.TensorConeNaturality

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

/-- The unit-cone comparison respects every morphism of the other tensor complex. -/
lemma cochainTensorUnitScalarConeIso_naturality (a : R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    cochainTensorMap (𝟙 (CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R))))) f ≫
        (cochainTensorUnitScalarConeIso a Q).hom =
      (cochainTensorUnitScalarConeIso a P).hom ≫ (scalarConeFunctor a).map f := by
  dsimp only [cochainTensorUnitScalarConeIso, Iso.trans_hom,
    homotopyCofiber.mapArrowIso_hom, scalarConeFunctor]
  rw [← Category.assoc, cochainTensorConeLeft_naturality_right]
  simp only [Category.assoc]
  congr 1
  rw [← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
  congr 1
  apply Arrow.hom_ext
  · change cochainTensorMap (𝟙 cochainTensorUnit) f ≫ (cochainTensorLeftUnitor Q).hom =
      (cochainTensorLeftUnitor P).hom ≫ f
    exact MonoidalCategory.leftUnitor_naturality f
  · change cochainTensorMap (𝟙 cochainTensorUnit) f ≫ (cochainTensorLeftUnitor Q).hom =
      (cochainTensorLeftUnitor P).hom ≫ f
    exact MonoidalCategory.leftUnitor_naturality f

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

/-- The tensor computation is natural in every morphism of actual derived objects. -/
lemma boundedAboveDerivedTensorQuotientKoszulIso_naturality
    (a : R) (ha : IsSMulRegular R a)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (derivedBaseChangeScalarObject (Ideal.Quotient.mk (Ideal.span {a})))) f)).hom ≫
        (boundedAboveDerivedTensorQuotientKoszulIso a ha Y).hom =
      (boundedAboveDerivedTensorQuotientKoszulIso a ha X).hom ≫
        (DerivedCompletion.derivedScalarConeFunctor R a).map f.hom := by
  let A := principalQuotientDerivedModel a ha
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  have hm := boundedAboveDerivedTensorModelIso_naturality A A P Q
    (𝟙 (derivedBaseChangeScalarObject (Ideal.Quotient.mk (Ideal.span {a})))) f
    (𝟙 A.complex) h (by simp) (P.map_naturality Q f.hom)
  have hc := (DerivedCompletion.derivedScalarConeComparison R a).inv.naturality h
  change DerivedCategory.Q.map ((scalarConeFunctor a).map h) ≫
      (DerivedCompletion.derivedScalarConeComparison R a).inv.app Q.complex =
    (DerivedCompletion.derivedScalarConeComparison R a).inv.app P.complex ≫
      (DerivedCompletion.derivedScalarConeFunctor R a).map (DerivedCategory.Q.map h) at hc
  simp only [boundedAboveDerivedTensorQuotientKoszulIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  congr 1
  dsimp only [A, principalQuotientDerivedModel]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    cochainTensorUnitScalarConeIso_naturality, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, hc, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (DerivedCompletion.derivedScalarConeFunctor R a).map
    (P.map_naturality Q f.hom)

/-- Restricted scalar extension and Koszul reduction agree naturally on all derived morphisms. -/
lemma restrictedDerivedQuotientKoszulIso_naturality (a : R) (ha : IsSMulRegular R a)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).map
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).map f)).hom ≫
        (restrictedDerivedQuotientKoszulIso a ha Y).hom =
      (restrictedDerivedQuotientKoszulIso a ha X).hom ≫
        (DerivedCompletion.derivedScalarConeFunctor R a).map f.hom := by
  have hn := congrArg (fun k => k.hom)
    (boundedAboveDerivedBaseChangeTensorIso_naturality (Ideal.Quotient.mk (Ideal.span {a})) f)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hn
  simp only [restrictedDerivedQuotientKoszulIso, Iso.trans_hom, Functor.mapIso_hom]
  change _ ≫
      (boundedAboveDerivedBaseChangeTensorIso (Ideal.Quotient.mk (Ideal.span {a})) Y).hom.hom ≫
      (boundedAboveDerivedTensorQuotientKoszulIso a ha Y).hom = _
  rw [← Category.assoc, hn, Category.assoc, boundedAboveDerivedTensorQuotientKoszulIso_naturality]
  simp only [Category.assoc]
  rfl

/-- Derived reduction along the regular principal quotient is the actual Koszul functor. -/
def restrictedDerivedQuotientKoszulNatIso (a : R) (ha : IsSMulRegular R a) :
    boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a})) ⋙
        boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a})) ⋙
        DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ DerivedCompletion.derivedScalarConeFunctor R a :=
  NatIso.ofComponents (restrictedDerivedQuotientKoszulIso a ha)
    (fun f => restrictedDerivedQuotientKoszulIso_naturality a ha f)

end SerrePositivity
