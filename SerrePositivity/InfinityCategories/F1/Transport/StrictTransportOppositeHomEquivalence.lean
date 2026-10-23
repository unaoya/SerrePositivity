module

public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportWeightedMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeUnstraighteningHomComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.UnstraighteningMappingEquivalence

/-!
概要：strict transport の像の反転 coherent 区間作用そのものは、全写像空間の同値。
方針：無条件の全 Hom 比較と元の weighted 作用の同値性を使い、両側の比較射を消去する。
規約：Kan 性は既存の strict transport の像の Hom から得て、追加の仮定を置かない。
使われ方：実際の分類写像の coherent な作用の充満忠実性を閉じる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

local instance strictTransportOppositeSourceKan {I : Type u} [SmallCategory I]
    (F G : StrictTransportDiagramObject I) :
    KanComplex (SimplicialCategory.sHom (strictTransportKanDiagramEnriched.obj F)
      (strictTransportKanDiagramEnriched.obj G)) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom F G))

/-- strict transport の像の反転図式の coherent な区間作用は、元の写像空間全体で同値。 -/
lemma strictTransportOppositeHomInterval_isQCatEquivalence
    {I : Type u} [SmallCategory I] (F G : StrictTransportDiagramObject I) :
    IsQCatEquivalence (kanDiagramOppositeHomInterval
      (strictTransportKanDiagramEnriched.obj F) (strictTransportKanDiagramEnriched.obj G)) := by
  let F' := strictTransportKanDiagramEnriched.obj F
  let G' := strictTransportKanDiagramEnriched.obj G
  have : KanComplex (SimplicialCategory.sHom F' G') :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom F G))
  have : ∀ i, KanComplex ((G'.val ⋙ kanObjectForget).obj i) :=
    fun i => (G'.val.obj i).isKanComplex
  let pG := leftUnstraighteningProjection
    (kanDiagramCoherentNerve (G'.val ⋙ kanObjectOpFunctor))
  let wF := (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveProjection (F'.val ⋙ kanObjectForget))
  let wG := (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveProjection (G'.val ⋙ kanObjectForget))
  have : LeftFibration wG :=
    leftFibration_uliftFunctor_map (weightedNerveProjection (G'.val ⋙ kanObjectForget))
  have hp := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    wG pG (oppositeKanUnstraighteningComparison G'.val)
    (oppositeKanUnstraighteningComparison_projection G'.val)
    (oppositeKanUnstraighteningComparison_isPrecompositionEquivalence G'.val) wF
  have hl : IsQCatEquivalence (oppositeUnstraighteningHomLeft F' G') :=
    (strictTransportCommonWeightedAction_isQCatEquivalence F G).comp hp
  have hr := hl.ofFunctorIso (oppositeUnstraighteningHomComparisonIso F' G').symm
  have hpre := relativeFunctorOverPre_isQCatEquivalence pG (oppositeKanUnstraighteningOverMap F')
    (oppositeKanUnstraighteningComparison_isPrecompositionEquivalence F'.val)
  have hu := leftUnstraighteningMappingSpaceMap_isQCatEquivalence
    (kanDiagramCoherentNerve (F'.val ⋙ kanObjectOpFunctor))
    (kanDiagramCoherentNerve (G'.val ⋙ kanObjectOpFunctor))
  have hwhole : IsQCatEquivalence (kanDiagramOppositeHomInterval F' G' ≫
      (leftUnstraighteningMappingSpaceMap
        (kanDiagramCoherentNerve (F'.val ⋙ kanObjectOpFunctor))
        (kanDiagramCoherentNerve (G'.val ⋙ kanObjectOpFunctor)) ≫
          relativeFunctorOverPre pG (oppositeKanUnstraighteningOverMap F'))) := by
    simpa only [oppositeUnstraighteningHomRight, Category.assoc] using hr
  exact (hu.comp hpre).cancel_right hwhole

end SerrePositivity.InfinityCategories
