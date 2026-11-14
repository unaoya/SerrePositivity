module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomProjectedEvaluation

/-!
概要：元の全Hom比較を同じ反転・AW・添字移送・実Hom同型に括り直す。
方針：既存の反転endの因数分解とΓ・反転関手の合成則を使う。
規約：IS-W2 B02の既存構成の合成則。比較射と指定輸送を保持する。
使われ方：HA 1.2.4、元のnative比較との全単体的射の等式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {A : Type u} [CommRing A]

/-- 元のΓ比較は指定反転end・small添字同型・実Hom同型との合成そのもの。 -/
theorem gammaReflectedBKComparison_factor (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P ((productTotalFunctor A).obj X) ≫
      (truncatedDoldKanFunctor A).map γ ≫
        normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) (normalizedBKCoefficientMap A)
    gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P) =
      SSet.opFunctor.map ψ ≫
        (weightedSectionsReflectedIso (normalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y ⋙ truncatedDoldKanFunctor A) ≪≫
            normalizedBKOriginalSectionsIso A Y).hom ≫
        (weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).map
          (normalizedBKReflectedHomDiagramIso X P).hom := by
  dsimp only
  rw [gammaReflectedBKComparison, normalizedBKReflectedSectionsMap,
    normalizedBKOriginalSectionsMap_factor]
  simp only [reflectedNormalizedBKSmallSectionsMap, normalizedBKReverseSpaceMap,
    normalizedBousfieldKanHomSpaceComparison, Functor.map_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
