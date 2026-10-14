module

public import SerrePositivity.Spectra.General.CotensorMappingSource
public import SerrePositivity.Spectra.General.ParametrizedCotensor

/-! # Parameter variance of C-valued cotensor mapping representability -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

lemma cotensorMappingAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K)
    (g : pointwiseTensor Y (pointwiseTensor Z E) ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        (pointwiseTensorPost f (pointwiseTensor Z E) ≫ g) =
      (cotensorMappingAdjunction Y E).homEquiv Z F g ≫
        (mappingObjectFunctor E).map ((cotensorBifunctor.map f.op).app F) := by
  unfold cotensorMappingAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change mappingObjectHomEquiv Z E ((cotensorFunctor X).obj F)
    (pointwiseTensorHomEquiv X (pointwiseTensor Z E) F
      (pointwiseTensorPost f (pointwiseTensor Z E) ≫ g)) = _
  rw [pointwiseTensorHomEquiv_naturality_parameter]
  rw [mappingObjectHomEquiv_naturality_target]
  rfl

lemma cotensorMappingPowerAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Y ⊗ Z) E ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv Z F (pointwiseTensorPost (f ▷ Z) E ≫ g) =
      (cotensorMappingPowerAdjunction Y E).homEquiv Z F g ≫
        (MonoidalClosed.pre f).app (mappingObject E F) := by
  unfold cotensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (ihom.adjunction X).homEquiv Z (mappingObject E F)
    (mappingObjectHomEquiv (X ⊗ Z) E F (pointwiseTensorPost (f ▷ Z) E ≫ g)) = _
  rw [mappingObjectHomEquiv_naturality_parameter]
  change MonoidalClosed.curry (f ▷ Z ≫ mappingObjectHomEquiv (Y ⊗ Z) E F g) =
    MonoidalClosed.curry (mappingObjectHomEquiv (Y ⊗ Z) E F g) ≫
      (MonoidalClosed.pre f).app (mappingObject E F)
  exact (MonoidalClosed.curry_pre_app f _).symm

/-- Cotensor mapping comparison is contravariantly natural in its parameter. -/
lemma cotensorMappingIso_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    (mappingObjectFunctor E).map ((cotensorBifunctor.map f.op).app F) ≫
        (cotensorMappingIso X E F).hom =
      (cotensorMappingIso Y E F).hom ≫ (MonoidalClosed.pre f).app (mappingObject E F) := by
  apply ActionComparisonNaturality.parameter
    (cotensorMappingAdjunction X E) (cotensorMappingAdjunction Y E)
    (cotensorMappingPowerAdjunction X E) (cotensorMappingPowerAdjunction Y E)
    (cotensorMappingParameterIso X E).symm (cotensorMappingParameterIso Y E).symm
    (fun Z ↦ pointwiseTensorPost f (pointwiseTensor Z E))
    (fun G ↦ (mappingObjectFunctor E).map ((cotensorBifunctor.map f.op).app G))
    (fun Z ↦ pointwiseTensorPost (f ▷ Z) E)
    (fun G ↦ (MonoidalClosed.pre f).app (mappingObject E G))
  · intro Z G g
    exact cotensorMappingAdjunction_naturality_parameter f Z E G g
  · intro Z G g
    exact cotensorMappingPowerAdjunction_naturality_parameter f Z E G g
  · intro Z
    change pointwiseTensorPost f (pointwiseTensor Z E) ≫
        (pointwiseTensorAssociator Y Z E).inv =
      (pointwiseTensorAssociator X Z E).inv ≫ pointwiseTensorPost (f ▷ Z) E
    apply (cancel_mono (pointwiseTensorAssociator Y Z E).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← tensorHom_id f Z, pointwiseTensorAssociator_parameter_left]
    simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.GeneralSymmetricSpectrum
