module

public import SerrePositivity.Spectra.General.Cotensor
public import SerrePositivity.CategoryTheory.Enriched.MonoidalAdjunction
public import SerrePositivity.CategoryTheory.Enriched.ActionEvaluation


/-! # C-valued mapping objects of general symmetric spectra

The zeroth level of the spectrum internal Hom represents the parameter tensor.
The ordinary Hom equivalence is obtained using the actual action unit, so the
existing category of spectra is retained. Enrichment laws are a further step.
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

abbrev mappingObjectFunctor (E : GeneralSymmetricSpectrum C K) :
    GeneralSymmetricSpectrum C K ⥤ C := internalHomFunctor E ⋙ evaluation 0

abbrev mappingObject (E F : GeneralSymmetricSpectrum C K) : C :=
  (mappingObjectFunctor E).obj F

def mappingObjectBifunctor : (GeneralSymmetricSpectrum C K)ᵒᵖ ⥤
    GeneralSymmetricSpectrum C K ⥤ C :=
  internalHomBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj (evaluation 0)

abbrev mappingTensorFunctor (E : GeneralSymmetricSpectrum C K) :
    C ⥤ GeneralSymmetricSpectrum C K := MappingUnitLaws.parameterFunctor pointwiseTensorBifunctor E

def mappingTensorNatIso (E : GeneralSymmetricSpectrum C K) :
    (freeAt 0) ⋙ tensorRight E ≅ mappingTensorFunctor E :=
  FunctorTransport.iso ((freeAt 0) ⋙ tensorRight E)
    (fun X ↦ pointwiseTensor X E) (fun X ↦ tensorFreeZeroPointwiseIso X E)

def mappingObjectAdjunction (E : GeneralSymmetricSpectrum C K) :
    mappingTensorFunctor E ⊣ mappingObjectFunctor E :=
  (MonoidalMappingAdjunction.adjunction (freeAtAdjunction 0) E).ofNatIsoLeft
    (mappingTensorNatIso E)

abbrev mappingObjectHomEquiv (X : C) (E F : GeneralSymmetricSpectrum C K) :
    (pointwiseTensor X E ⟶ F) ≃ (X ⟶ mappingObject E F) :=
  (mappingObjectAdjunction E).homEquiv X F

/-- Ordinary maps are the unit-valued points of the mapping object. -/
def ordinaryHomEquiv (E F : GeneralSymmetricSpectrum C K) :
    (E ⟶ F) ≃ (𝟙_ C ⟶ mappingObject E F) :=
  (Iso.homCongr (pointwiseTensorUnitNatIso.app E).symm (Iso.refl F)).trans
    ((mappingObjectAdjunction E).homEquiv (𝟙_ C) F)

/-- The two represented adjunctions identify the same ordinary mapping points. -/
def cotensorMappingHomEquiv (X : C) (E F : GeneralSymmetricSpectrum C K) :
    (E ⟶ cotensor X F) ≃ (X ⟶ mappingObject E F) :=
  (pointwiseTensorHomEquiv X E F).symm.trans (mappingObjectHomEquiv X E F)

lemma mappingHom_compatibility (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    cotensorMappingHomEquiv X E F (pointwiseTensorHomEquiv X E F f) =
      mappingObjectHomEquiv X E F f := by
  simp [cotensorMappingHomEquiv]
lemma mappingObjectHomEquiv_naturality_parameter {X Y : C} (a : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor Y E ⟶ F) :
    mappingObjectHomEquiv X E F ((pointwiseTensorBifunctor.map a).app E ≫ f) =
      a ≫ mappingObjectHomEquiv Y E F f :=
  (mappingObjectAdjunction E).homEquiv_naturality_left a f

lemma mappingObjectHomEquiv_naturality_target (X : C) (E : GeneralSymmetricSpectrum C K)
    {F F' : GeneralSymmetricSpectrum C K} (b : F ⟶ F') (f : pointwiseTensor X E ⟶ F) :
    mappingObjectHomEquiv X E F' (f ≫ b) =
      mappingObjectHomEquiv X E F f ≫ (mappingObjectFunctor E).map b :=
  (mappingObjectAdjunction E).homEquiv_naturality_right f b
end SerrePositivity.GeneralSymmetricSpectrum
