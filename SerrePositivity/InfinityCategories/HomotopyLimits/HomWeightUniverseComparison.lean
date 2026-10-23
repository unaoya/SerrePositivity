module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseYonedaComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights

/-!
概要：元の Hom 係数前層族の指定宇宙変更を、全体を持ち上げた元の図式の係数族へ比較。
方針：元の全 Yoneda 宇宙比較と、元の全前層制限との厳密な可換性を合成する。
規約：全 C と全標的の自然性を保持し、値ごとの同値で代用しない。
使われ方：元の係数評価と、持ち上げた標的の全 Hom 族との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全 Hom 係数族の宇宙変更は、持ち上げた元の図式の全係数族と自然同型。 -/
def presheafHomWeightDiagram_universeIso {C D : SSet.{u}} [Quasicategory D] (F : C ⟶ D) :
    FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (presheafHomWeightDiagram F) ≫
      presheafUniverseDiagram C)
      (presheafHomWeightDiagram ((SSet.uliftFunctor.{u + 1, u}).map F)) := by
  have e := (yonedaInfinityMap_universeIso D).postcomp
    (presheafInfinityRestriction ((SSet.uliftFunctor.{u + 1, u}).map F))
  change FunctorIso _ (presheafHomWeightDiagram ((SSet.uliftFunctor.{u + 1, u}).map F)) at e
  dsimp only [presheafHomWeightDiagram]
  rw [CategoryTheory.Functor.map_comp, Category.assoc, presheafUniverseDiagram_restriction]
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
