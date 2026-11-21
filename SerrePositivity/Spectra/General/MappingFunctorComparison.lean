module

public import SerrePositivity.Spectra.General.MappingEnrichment
public import SerrePositivity.CategoryTheory.Enriched.AdjunctionDataHomFunctor
public import SerrePositivity.Spectra.General.ParametrizedMapping

/-! # Functoriality of the general enriched mapping objects -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- Postcomposition with an ordinary spectrum map is the existing mapping map. -/
lemma mappingObjectComposition_post (E : GeneralSymmetricSpectrum C K)
    {F G : GeneralSymmetricSpectrum C K} (g : F ⟶ G) :
    (λ_ (mappingObject E F)).inv ≫ mappingObjectArrow g ▷ mappingObject E F ≫
      mappingObjectComposition E F G = (mappingObjectFunctor E).map g := by
  apply MappingWhiskering.post_composition pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction g
  · exact pointwiseTensorAssociator_parameter_left (mappingObjectArrow g)
      (mappingObject E F) E
  · exact pointwiseTensor_left_unit (mappingObject E F) E

/-- Precomposition by an ordinary spectrum map is the existing source map. -/
lemma mappingObjectComposition_pre {E F : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (G : GeneralSymmetricSpectrum C K) :
    (ρ_ (mappingObject F G)).inv ≫ mappingObject F G ◁ mappingObjectArrow f ≫
      mappingObjectComposition E F G = (mappingObjectBifunctor.map f.op).app G := by
  have h := MappingWhiskering.pre_composition pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction f
    (pointwiseTensorAssociator_parameter_right (mappingObject F G) (mappingObjectArrow f) E)
    (pointwiseTensor_triangle (mappingObject F G) E)
  change (ρ_ (mappingObject F G)).inv ≫ mappingObject F G ◁ mappingObjectArrow f ≫
    mappingObjectComposition E F G =
      mappingObjectHomEquiv (mappingObject F G) E G
        ((pointwiseTensorFunctor (mappingObject F G)).map f ≫ mappingObjectEvaluation F G) at h
  rw [h, mappingObjectHomEquiv_naturality_source]
  have hc : mappingObjectHomEquiv (mappingObject F G) F G (mappingObjectEvaluation F G) =
      𝟙 (mappingObject F G) := by
    exact ((mappingObjectAdjunction F).homEquiv _ G).eq_symm_apply.mp
      ((mappingObjectAdjunction F).homEquiv_symm_id G).symm
  rw [hc, Category.id_comp]

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

/-- The enriched right whiskering agrees on whole objects, not just unit points. -/
lemma eHomWhiskerLeft_eq_mappingObjectMap (E : GeneralSymmetricSpectrum C K)
    {F G : GeneralSymmetricSpectrum C K} (g : F ⟶ G) :
    eHomWhiskerLeft C E g = (mappingObjectFunctor E).map g := by
  change (ρ_ (mappingObject E F)).inv ≫ mappingObject E F ◁ mappingObjectArrow g ≫
    (β_ (mappingObject E F) (mappingObject F G)).hom ≫ mappingObjectComposition E F G = _
  rw [BraidedCategory.braiding_naturality_right_assoc,
    ← Category.assoc, rightUnitor_inv_braiding]
  exact mappingObjectComposition_post E g

/-- The enriched source whiskering is the existing contravariant source map. -/
lemma eHomWhiskerRight_eq_mappingObjectMap {E F : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (G : GeneralSymmetricSpectrum C K) :
    eHomWhiskerRight C f G = (mappingObjectBifunctor.map f.op).app G := by
  change (λ_ (mappingObject F G)).inv ≫ mappingObjectArrow f ▷ mappingObject F G ≫
    (β_ (mappingObject E F) (mappingObject F G)).hom ≫ mappingObjectComposition E F G = _
  rw [BraidedCategory.braiding_naturality_left_assoc,
    ← Category.assoc, leftUnitor_inv_braiding]
  exact mappingObjectComposition_pre f G

/-- Comparison in both spectrum variables with the chosen enriched Hom functor. -/
def mappingEnrichedHomFunctorIso :
    eHomFunctor C (GeneralSymmetricSpectrum C K) ≅ mappingObjectBifunctor :=
  NatIso.ofComponents (fun E ↦ NatIso.ofComponents (fun F ↦ Iso.refl (mappingObject E.unop F))
    (fun g ↦ by
      change eHomWhiskerLeft C E.unop g ≫ 𝟙 _ = 𝟙 _ ≫ (mappingObjectFunctor E.unop).map g
      rw [eHomWhiskerLeft_eq_mappingObjectMap, Category.comp_id, Category.id_comp]))
    (fun f ↦ by
      apply NatTrans.ext
      funext G
      change eHomWhiskerRight C f.unop G ≫ 𝟙 _ =
        𝟙 _ ≫ (mappingObjectBifunctor.map f).app G
      rw [eHomWhiskerRight_eq_mappingObjectMap, Category.comp_id, Category.id_comp]
      rfl)

end SerrePositivity.GeneralSymmetricSpectrum
