module

public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.DerivedTensorCoherenceModels
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.HomologicalAlgebra.CochainTensorScalarCone
public import SerrePositivity.HomologicalAlgebra.DerivedTensorMonoidal

/-! # Tensor realization of scalar Koszul reduction, without regularity -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual two-term Koszul object on any scalar, including zero divisors. -/
def boundedAboveKoszulObject (a : R) : DerivedCategory.Minus (ModuleCat.{u} R) :=
  boundedAboveDerivedConeObject boundedAboveDerivedTensorUnitModel
    boundedAboveDerivedTensorUnitModel (smulId a cochainTensorUnit)

/-- Its canonical finite free model is the actual unit scalar cone. -/
def boundedAboveKoszulModel (a : R) :
    BoundedAboveDerivedModel (boundedAboveKoszulObject a).obj :=
  boundedAboveDerivedTensorUnitModel.cone boundedAboveDerivedTensorUnitModel
    (smulId a cochainTensorUnit)

/-- Derived tensor with the two-term Koszul object computes actual scalar reduction. -/
def boundedAboveDerivedTensorKoszulIso (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedTensor.obj (boundedAboveKoszulObject a, X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor R a).obj X.obj :=
  boundedAboveDerivedTensorModelIso _ _ (boundedAboveKoszulModel a)
      (boundedAboveDerivedChosenModel X) ≪≫
    DerivedCategory.Q.mapIso (cochainTensorUnitScalarConeIso a
      (boundedAboveDerivedChosenModel X).complex) ≪≫
    (DerivedCompletion.derivedScalarConeComparison R a).symm.app
      (boundedAboveDerivedChosenModel X).complex ≪≫
    (DerivedCompletion.derivedScalarConeFunctor R a).mapIso
      (boundedAboveDerivedChosenModel X).iso

/-- The tensor-to-Koszul comparison respects every actual derived morphism. -/
theorem boundedAboveDerivedTensorKoszulIso_naturality (a : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveKoszulObject a)) f)).hom ≫
        (boundedAboveDerivedTensorKoszulIso a Y).hom =
      (boundedAboveDerivedTensorKoszulIso a X).hom ≫
        (DerivedCompletion.derivedScalarConeFunctor R a).map f.hom := by
  let A := boundedAboveKoszulModel a
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  have hm := boundedAboveDerivedTensorModelIso_naturality A A P Q
    (𝟙 (boundedAboveKoszulObject a)) f
    (𝟙 A.complex) h (by simp [A, boundedAboveKoszulModel, BoundedAboveDerivedModel.cone])
    (P.map_naturality Q f.hom)
  have hc := (DerivedCompletion.derivedScalarConeComparison R a).inv.naturality h
  change DerivedCategory.Q.map ((scalarConeFunctor a).map h) ≫
      (DerivedCompletion.derivedScalarConeComparison R a).inv.app Q.complex =
    (DerivedCompletion.derivedScalarConeComparison R a).inv.app P.complex ≫
      (DerivedCompletion.derivedScalarConeFunctor R a).map (DerivedCategory.Q.map h) at hc
  simp only [boundedAboveDerivedTensorKoszulIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  congr 1
  dsimp only [A, boundedAboveKoszulModel, BoundedAboveDerivedModel.cone,
    boundedAboveDerivedTensorUnitModel]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    cochainTensorUnitScalarConeIso_naturality, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, hc, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (DerivedCompletion.derivedScalarConeFunctor R a).map
    (P.map_naturality Q f.hom)

/-- Tensoring by the actual finite Koszul object realizes the scalar-cone functor naturally. -/
def boundedAboveDerivedTensorKoszulNatIso (a : R) :
    tensorLeft (boundedAboveKoszulObject a) ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ DerivedCompletion.derivedScalarConeFunctor R a :=
  NatIso.ofComponents (boundedAboveDerivedTensorKoszulIso a)
    (fun f ↦ boundedAboveDerivedTensorKoszulIso_naturality a f)

/-- Isomorphisms of actual scalar reductions can be tested by derived Koszul tensor. -/
theorem boundedAboveDerivedTensorKoszul_isIso_iff (a : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    IsIso (boundedAboveKoszulObject a ◁ f) ↔
      IsIso ((DerivedCompletion.derivedScalarConeFunctor R a).map f.hom) := by
  constructor
  · intro h
    exact (NatIso.isIso_map_iff (boundedAboveDerivedTensorKoszulNatIso a) f).mp (by
      change IsIso (DerivedCategory.Minus.ι.map (boundedAboveKoszulObject a ◁ f))
      infer_instance)
  · intro h
    have : IsIso (DerivedCategory.Minus.ι.map (boundedAboveKoszulObject a ◁ f)) :=
      (NatIso.isIso_map_iff (boundedAboveDerivedTensorKoszulNatIso a) f).mpr h
    exact isIso_of_reflects_iso _ DerivedCategory.Minus.ι

end SerrePositivity
