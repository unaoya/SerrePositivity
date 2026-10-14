module

public import SerrePositivity.Spectra.General.TensorMappingSource

/-! # Parameter variance of C-valued tensor mapping representability -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- The right-tensor power adjunction is contravariantly natural in its tensor parameter. -/
lemma tensorMappingPowerAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Z ⊗ Y) E ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv Z F (pointwiseTensorPost (Z ◁ f) E ≫ g) =
      (tensorMappingPowerAdjunction Y E).homEquiv Z F g ≫
        (MonoidalClosed.pre f).app (mappingObject E F) := by
  unfold tensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (((ihom.adjunction X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv Z _)
      (mappingObjectHomEquiv (Z ⊗ X) E F (pointwiseTensorPost (Z ◁ f) E ≫ g)) = _
  rw [mappingObjectHomEquiv_naturality_parameter]
  change (((ihom.adjunction X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv Z (mappingObject E F))
      (Z ◁ f ≫ mappingObjectHomEquiv (Z ⊗ Y) E F g) =
    (((ihom.adjunction Y).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv Z (mappingObject E F))
        (mappingObjectHomEquiv (Z ⊗ Y) E F g) ≫ (MonoidalClosed.pre f).app (mappingObject E F)
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change MonoidalClosed.curry ((β_ X Z).hom ≫ Z ◁ f ≫
      mappingObjectHomEquiv (Z ⊗ Y) E F g) =
    MonoidalClosed.curry ((β_ Y Z).hom ≫ mappingObjectHomEquiv (Z ⊗ Y) E F g) ≫
      (MonoidalClosed.pre f).app (mappingObject E F)
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc,
    ← MonoidalClosed.curry_pre_app]

/-- The C-valued tensor mapping comparison is contravariantly natural in its parameter. -/
lemma tensorMappingIso_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map (pointwiseTensorPost f E).op).app F ≫
        (tensorMappingIso X E F).hom =
      (tensorMappingIso Y E F).hom ≫ (MonoidalClosed.pre f).app (mappingObject E F) := by
  apply ActionComparisonNaturality.parameter
    (mappingObjectAdjunction (pointwiseTensor X E))
    (mappingObjectAdjunction (pointwiseTensor Y E))
    (tensorMappingPowerAdjunction X E) (tensorMappingPowerAdjunction Y E)
    (tensorMappingParameterIso X E).symm (tensorMappingParameterIso Y E).symm
    (fun Z ↦ (pointwiseTensorFunctor Z).map (pointwiseTensorPost f E))
    (fun G ↦ (mappingObjectBifunctor.map (pointwiseTensorPost f E).op).app G)
    (fun Z ↦ pointwiseTensorPost (Z ◁ f) E)
    (fun G ↦ (MonoidalClosed.pre f).app (mappingObject E G))
  · intro Z G g
    exact mappingObjectHomEquiv_naturality_source Z (pointwiseTensorPost f E) G g
  · intro Z G g
    exact tensorMappingPowerAdjunction_naturality_parameter f Z E G g
  · intro Z
    change (pointwiseTensorFunctor Z).map (pointwiseTensorPost f E) ≫
        (pointwiseTensorAssociator Z Y E).inv =
      (pointwiseTensorAssociator Z X E).inv ≫ pointwiseTensorPost (Z ◁ f) E
    apply (cancel_mono (pointwiseTensorAssociator Z Y E).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← id_tensorHom Z f, pointwiseTensorAssociator_parameter_right]
    simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.GeneralSymmetricSpectrum
