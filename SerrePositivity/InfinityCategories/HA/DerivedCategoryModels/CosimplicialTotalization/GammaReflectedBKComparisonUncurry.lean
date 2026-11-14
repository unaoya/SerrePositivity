module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparisonFactor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKNormalizedSectionsMapEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SmallBKIndexSectionsEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedSectionsReflectionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsDiagramNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedHomComparison

/-!
概要：元のΓ比較のuncurryを、同じnative錐の実豊穣合成の族へ照合する。
方針：既存の反転・small添字・前後合成の評価則を同じ全uncurry式に適用する。
規約：IS-W2 B02の証明分割。元の頂点・錐入力・全単体的射を保持する。
使われ方：HA 1.2.4、G10の同じnative比較の同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {A : Type u} [CommRing A]

/-- 元の全Hom比較のuncurryは、元のnative錐入力との実合成の同じ族。 -/
theorem gammaReflectedBKComparison_uncurry (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} SimplexCategory) :
    (weightedSectionsUncurry
      (gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P))).app j =
    (reflectedWeightedHomFamily (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (liftedEnrichedBousfieldKanCone X) (ForgetEnrichment.of (Complex A) P)).app j := by
  rw [gammaReflectedBKComparison_factor]
  dsimp only [normalizedBKOriginalSectionsIso, Iso.trans_hom,
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsWeightIso,
    weightedSectionsFunctor, smallBKIndexSectionsIso]
  rw [smallBousfieldKanWeightIso_hom]
  simp only [← Category.assoc]
  rw [weightedSectionsUncurry_postcomp]
  simp only [NatTrans.comp_app]
  rw [weightedSectionsUncurry_comp_pre]
  simp only [NatTrans.comp_app]
  rw [smallBKIndexSectionsMap_uncurry, weightedSectionsReflectedIso_uncurry]
  simp only [Category.assoc]
  erw [reflectedBKNormalizedSections_uncurry_map]
  let Q := X.obj (AsSmall.down.obj j)
  let e := doldKanSimplicialHomIso (R := A) (D := Complex A)
    (ForgetEnrichment.of (Complex A) P) (ForgetEnrichment.of (Complex A) Q)
  have hη : (normalizedBKReflectedHomDiagramIso X P).hom.app j =
      SSet.opFunctor.map e.inv := rfl
  have he : standardDoldKanSpaceMap P Q = e.hom := rfl
  erw [hη, he]
  have hc : SSet.opFunctor.map e.hom ≫ SSet.opFunctor.map e.inv = 𝟙 _ := by
    rw [← SSet.opFunctor.map_comp, e.hom_inv_id, SSet.opFunctor.map_id]
  simp only [Functor.map_comp, Category.assoc, hc]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨w, α⟩
  dsimp only [reflectedWeightedHomFamily, liftedEnrichedBousfieldKanCone,
    enrichedBousfieldKanCone, reflectedPointwiseBousfieldKanCone,
    bousfieldKanEnrichedHomIso, complexDoldKanHomIso,
    NatIso.ofComponents, Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
    NatTrans.comp_app]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
