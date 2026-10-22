module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftFibrationSections
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningUnderComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeFunctorImage

/-!
概要：strict 図式の実際の分類像を、底の全単体上の相対切断の一つの coherent な系として回収する。
方針：既存の共同分類の制限同型を元の全図式へ前合成し、同じ豊穣図式の通常の実現へ移す。
規約：全単体・全添字の同じ関手同型。各頂点での比較の選択ではない。
使われ方：共同 weighted 分類との大域比較を、同じ相対切断の系に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {I J : Type u} [Category.{u} I] [Category.{u} J] {B : SSet.{u}}
  (F : I ⥤ LeftFibrationObject B)

/-- 全切断の豊穣図式を元の strict 図式で制限した、同じ Kan 図式値の通常の図式。 -/
def strictLeftSectionKanDiagramFamily (A : Jᵒᵖ ⥤ Over B) : I ⥤ KanDiagramObject J :=
  F ⋙ coherentEnrichedUnderlyingFunctor (relativeSectionEnrichedDiagram A).toEnrichedFunctor

/-- 同じ全切断の共同実現は、同じ Kan 図式値の通常の図式の実現と厳密に一致する。 -/
lemma strictLeftSectionKanDiagramFamily_realization (A : Jᵒᵖ ⥤ Over B) :
    strictCoherentDiagram F ≫ (relativeSectionEnrichedDiagram A).realization =
      strictCoherentDiagram (strictLeftSectionKanDiagramFamily F A) ≫
        kanDiagramRealization J := by
  rw [KanEnrichedDiagram.realization, ← Category.assoc, strictCoherentDiagram_postcomp]
  rfl

/-- 元の同じ分類像を初頂点写像で制限すると、全単体上の同じ切断図式の実現と関手同型。 -/
def strictLeftClassificationSectionIso :
    FunctorIso
      (strictCoherentDiagram F ≫ leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (strictCoherentDiagram
        (strictLeftSectionKanDiagramFamily F (transportSimplexDomainFunctor B)) ≫
          kanDiagramRealization (TransportSimplexCategory B)) := by
  have h := (leftStraighteningInfinityMap_restrictIso B).precomp (strictCoherentDiagram F)
  rw [transportSimplexSectionInfinity, relativeSectionDiagramInfinity,
    internalHomFlipHomEquiv_transposeFunctorFamily,
    strictLeftSectionKanDiagramFamily_realization] at h
  exact h

/-- 固定した底の図式の相対切断も、同じ元の strict 図式の実際の豊穣評価から回収する。 -/
lemma strictLeftFibrationSectionDiagram_coherent {A : SSet.{u}} (a : A ⟶ B) :
    strictCoherentDiagram F ≫ coherentNerveMap (relativeFunctorEnrichedEvaluation (Over.mk a)) =
      kanDiagramCoherentNerve (strictLeftFibrationSectionDiagram F a) := by
  rw [strictCoherentDiagram_postcomp]
  exact strictCoherentDiagram_eq_kanDiagram _

end SerrePositivity.InfinityCategories.F2.Ind
