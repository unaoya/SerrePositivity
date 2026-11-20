module

public import SerrePositivity.Spectra.General.TensorCotensorEnriched
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Mapping-object representability of the general spectrum cotensor

Composing the mapping and cotensor adjunctions and comparing left adjoints gives
an isomorphism of C-valued Hom objects, natural in the target spectrum.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- The other associativity comparison, natural in the mapping parameter. -/
def cotensorMappingParameterIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorLeft X ⋙ mappingTensorFunctor E ≅ mappingTensorFunctor E ⋙ pointwiseTensorFunctor X :=
  NatIso.ofComponents (fun Z ↦ pointwiseTensorAssociator X Z E) (fun f ↦ by
    change pointwiseTensorPost (X ◁ f) E ≫ (pointwiseTensorAssociator X _ E).hom =
      (pointwiseTensorAssociator X _ E).hom ≫
        (pointwiseTensorFunctor X).map (pointwiseTensorPost f E)
    rw [← id_tensorHom X f]
    exact pointwiseTensorAssociator_parameter_right X f E)

/-- The composite right adjoint is the mapping object of the cotensor. -/
def cotensorMappingAdjunction (X : C) (E : GeneralSymmetricSpectrum C K) :
    mappingTensorFunctor E ⋙ pointwiseTensorFunctor X ⊣
      cotensorFunctor X ⋙ mappingObjectFunctor E :=
  (mappingObjectAdjunction E).comp (pointwiseTensorCotensorAdjunction X)

/-- The same power object is represented by left tensor of the parameter. -/
def cotensorMappingPowerAdjunction (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorLeft X ⋙ mappingTensorFunctor E ⊣ mappingObjectFunctor E ⋙ ihom X :=
  (ihom.adjunction X).comp (mappingObjectAdjunction E)

/-- C-valued cotensor representability, natural in the target spectrum. -/
def cotensorMappingNatIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    cotensorFunctor X ⋙ mappingObjectFunctor E ≅ mappingObjectFunctor E ⋙ ihom X :=
  ActionComparisonAdjunction.rightIso (cotensorMappingAdjunction X E)
    (cotensorMappingPowerAdjunction X E) (cotensorMappingParameterIso X E).symm

abbrev cotensorMappingIso (X : C) (E F : GeneralSymmetricSpectrum C K) :
    mappingObject E (cotensor X F) ≅ (ihom X).obj (mappingObject E F) :=
  (cotensorMappingNatIso X E).app F

/-- The comparison respects transposition for every generalized parameter. -/
lemma cotensorMappingNatIso_homEquiv (X Z : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor (X ⊗ Z) E ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        ((pointwiseTensorAssociator X Z E).inv ≫ f) ≫ (cotensorMappingIso X E F).hom =
      (cotensorMappingPowerAdjunction X E).homEquiv Z F f :=
  ActionComparisonAdjunction.rightIso_homEquiv (cotensorMappingAdjunction X E)
    (cotensorMappingPowerAdjunction X E) (cotensorMappingParameterIso X E).symm Z F f

end SerrePositivity.GeneralSymmetricSpectrum
