module

public import SerrePositivity.Spectra.General.TensorCotensorEnriched
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Mapping-object representability of the general spectrum tensor

The action associator compares left adjoints. Uniqueness of right adjoints gives
an isomorphism of C-valued mapping objects, natural in the target spectrum.
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

/-- Associativity of the action, natural in an arbitrary mapping parameter. -/
def tensorMappingParameterIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorRight X ⋙ mappingTensorFunctor E ≅ mappingTensorFunctor (pointwiseTensor X E) :=
  NatIso.ofComponents (fun Z ↦ pointwiseTensorAssociator Z X E) (fun f ↦ by
    change pointwiseTensorPost (f ▷ X) E ≫ (pointwiseTensorAssociator _ X E).hom =
      (pointwiseTensorAssociator _ X E).hom ≫ pointwiseTensorPost f (pointwiseTensor X E)
    rw [← tensorHom_id f X]
    exact pointwiseTensorAssociator_parameter_left f X E)

/-- The right adjoint of the parameter functor composed with right tensor. -/
def tensorMappingPowerAdjunction (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorRight X ⋙ mappingTensorFunctor E ⊣ mappingObjectFunctor E ⋙ ihom X :=
  ((ihom.adjunction X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X)).comp
    (mappingObjectAdjunction E)

/-- C-valued tensor representability, natural in the target spectrum. -/
def tensorMappingNatIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    mappingObjectFunctor (pointwiseTensor X E) ≅ mappingObjectFunctor E ⋙ ihom X :=
  ActionComparisonAdjunction.rightIso (mappingObjectAdjunction (pointwiseTensor X E))
    (tensorMappingPowerAdjunction X E) (tensorMappingParameterIso X E).symm

/-- The component is an actual C-valued Hom-object isomorphism. -/
abbrev tensorMappingIso (X : C) (E F : GeneralSymmetricSpectrum C K) :
    mappingObject (pointwiseTensor X E) F ≅ (ihom X).obj (mappingObject E F) :=
  (tensorMappingNatIso X E).app F

/-- The comparison preserves transposition for arbitrary C-valued parameters. -/
lemma tensorMappingNatIso_homEquiv (X Z : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor (Z ⊗ X) E ⟶ F) :
    mappingObjectHomEquiv Z (pointwiseTensor X E) F
        ((pointwiseTensorAssociator Z X E).inv ≫ f) ≫ (tensorMappingIso X E F).hom =
      (tensorMappingPowerAdjunction X E).homEquiv Z F f :=
  ActionComparisonAdjunction.rightIso_homEquiv
    (mappingObjectAdjunction (pointwiseTensor X E)) (tensorMappingPowerAdjunction X E)
    (tensorMappingParameterIso X E).symm Z F f

end SerrePositivity.GeneralSymmetricSpectrum
