module

public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Spectrum-parameter naturality of mapping-object representability -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- The same Hom equivalence is natural in its spectrum source. -/
lemma mappingObjectHomEquiv_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (a : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor X E' ⟶ F) :
    mappingObjectHomEquiv X E F ((pointwiseTensorFunctor X).map a ≫ g) =
      mappingObjectHomEquiv X E' F g ≫ (mappingObjectBifunctor.map a.op).app F := by
  apply MonoidalMappingAdjunction.transported_pre (freeAtAdjunction 0) a
    (mappingTensorNatIso E') (mappingTensorNatIso E)
    ((pointwiseTensorFunctor X).map a) g
  exact (tensorFreeZeroPointwiseNatIso X).hom.naturality a

/-- The mapping object represents the action as a full parametrized adjunction. -/
def pointwiseTensorMappingParametrizedAdjunction :
    (pointwiseTensorBifunctor (K := K)).flip ⊣₂ mappingObjectBifunctor := by
  refine ParametrizedAdjunction.mk' (fun E ↦ mappingObjectAdjunction E) ?_
  intro E E' a X F g
  exact mappingObjectHomEquiv_naturality_source X a F g

end SerrePositivity.GeneralSymmetricSpectrum
