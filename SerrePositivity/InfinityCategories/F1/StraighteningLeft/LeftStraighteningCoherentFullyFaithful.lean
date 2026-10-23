module

public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportOppositeHomEquivalence
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramHomIntervalCriterion
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomIntervalPrecomposition
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveStraighteningUnit
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso

/-!
概要：通常の圏の nerve 上で、実際の coherent straightening の充満忠実性を証明する。
方針：strict transport の反転区間作用を同じ共同実現の Hom 作用へ移し、反転実現の比較を戻す。
規約：元の leftStraighteningCoherentMap を結論に固定し、単位・余単位を仮定しない。
使われ方：初頂点制限と局所化から任意の底の実際の分類写像の充満忠実性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- strict transport の像へ制限した同じ反転共同実現は充満忠実。 -/
lemma strictTransportOppositeRealization_isFullyFaithful (I : Type u) [SmallCategory I] :
    IsFullyFaithful (((kanDiagramUniversalEnriched I).opposite.precompose
      (edgewiseEnrichedFunctor (strictTransportKanDiagramEnriched (C := I)))).realization) := by
  apply KanEnrichedDiagram.isFullyFaithful_of_homInterval
  intro X Y
  rw [kanEnrichedDiagramHomInterval_precompose]
  have hm : (edgewiseEnrichedFunctor (strictTransportKanDiagramEnriched (C := I))).map X Y =
      𝟙 (edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)) :=
    edgewiseSubdivisionFunctor.map_id _
  have : IsIso ((edgewiseEnrichedFunctor
      (strictTransportKanDiagramEnriched (C := I))).map X Y) := by
    rw [hm]
    infer_instance
  have : KanComplex (SimplicialCategory.sHom
      ((edgewiseEnrichedFunctor (strictTransportKanDiagramEnriched (C := I))).obj X)
      ((edgewiseEnrichedFunctor (strictTransportKanDiagramEnriched (C := I))).obj Y)) :=
    inferInstanceAs (KanComplex (edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)))
  let m := (SSet.uliftFunctor.{u + 1, u}).map
    ((edgewiseEnrichedFunctor (strictTransportKanDiagramEnriched (C := I))).map X Y)
  have he := (qCatEquivalenceOfIso (asIso m)).isQCatEquivalence
  exact he.comp (strictTransportOppositeHomInterval_isQCatEquivalence X.val Y.val)

/-- strict transport の像の元の共同実現そのものは充満忠実。 -/
lemma strictTransportDiagramRealization_isFullyFaithful (I : Type u) [SmallCategory I] :
    IsFullyFaithful (strictTransportDiagramRealization I) := by
  let R := strictTransportKanDiagramEnriched (C := I)
  have h := strictTransportOppositeRealization_isFullyFaithful I
  rw [KanEnrichedDiagram.realization_precompose] at h
  have e := ((kanDiagramUniversalEnriched I).oppositeRealizationIso).precomp
    (coherentNerveMap (edgewiseEnrichedFunctor R))
  have hr : (kanDiagramUniversalEnriched I).realization = kanDiagramRealization I := by
    rw [KanEnrichedDiagram.realization, kanDiagramUniversalEnriched_toEnrichedFunctor,
      coherentNerveMap_id, Category.id_comp]
  rw [← Category.assoc, edgewiseEnrichedFunctor_infinity_right R, Category.assoc, hr,
    strictTransportKanDiagramEnriched_realization] at e
  have hpre : IsFullyFaithful (edgewiseEnrichedInfinityMap (StrictTransportDiagramObject I) ≫
      strictTransportDiagramRealization I) := e.isFullyFaithful_iff.mpr h
  let k := edgewiseEnrichedInfinityEquivalence (StrictTransportDiagramObject I)
  have hi : FunctorIso (k.inv ≫ (k.hom ≫ strictTransportDiagramRealization I))
      (strictTransportDiagramRealization I) := by
    simpa only [Category.assoc, Category.id_comp] using
      k.invHomIso.postcomp (strictTransportDiagramRealization I)
  exact hi.isFullyFaithful_iff.mp (k.symm.isQCatEquivalence.isFullyFaithful.comp hpre)

/-- 通常の圏の nerve 上で、元の coherent straightening 写像は充満忠実。 -/
lemma leftStraighteningCoherentMap_isFullyFaithful (I : Type u) [SmallCategory I] :
    IsFullyFaithful (leftStraighteningCoherentMap I) := by
  rw [← leftStrictTransportInfinityMap_realization I]
  exact (leftStrictTransportInfinityMap_isFullyFaithful I).comp
    (strictTransportDiagramRealization_isFullyFaithful I)

end SerrePositivity.InfinityCategories
