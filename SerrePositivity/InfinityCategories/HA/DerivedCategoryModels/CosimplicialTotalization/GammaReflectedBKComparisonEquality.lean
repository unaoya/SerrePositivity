module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparisonUncurry

/-!
概要：元のΓ比較は指定native錐の実豊穣Hom比較そのもので、同じ射が同値である。
方針：全uncurryの等式を切断の普遍性へ戻し、既存のΓ比較の同値性を代入する。
規約：IS-W2 B02・B03。元の全単体的射と同じnative錐・全試験対象を保持する。
使われ方：HA 1.2.4、G10の指定native錐の極限性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {A : Type u} [CommRing A]

/-- 元の全Γ比較は、同じ指定錐入力との実豊穣合成による比較そのもの。 -/
theorem gammaReflectedBKComparison_eq (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    gammaReflectedBKComparison X x =
      reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x := by
  apply (weightedSectionsHomEquiv (bousfieldKanWeight (AsSmall.{u} SimplexCategory))
    (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)
    (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op).injective
  change weightedSectionsUncurry (gammaReflectedBKComparison X x) =
    weightedSectionsUncurry (weightedSectionsLift
      (reflectedWeightedHomFamily (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x))
  rw [weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext j
  exact gammaReflectedBKComparison_uncurry (ForgetEnrichment.to (Complex A) x) X j

/-- 同じ指定native豊穣Hom比較自身が単体的ホモトピー同値。 -/
theorem reflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x) := by
  rw [← gammaReflectedBKComparison_eq]
  exact gammaReflectedBKComparison_equivalence X x

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
