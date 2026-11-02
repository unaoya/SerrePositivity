module

public import SerrePositivity.InfinityCategories.F1B.Ind.InitialBoundaryCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeHomUniversal
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFunctorInitialBoundary

/-!
概要：元の共同分類を持つ同じ相対 join 族の native 全余錐空間を比較する。
方針：実際の全 fiber 余極限性を相対境界充填へ渡し、全余錐の制限同値を得る。
規約：左 Kan 像も同じ全図式の後合成。使われ方：native な Kan 合成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op (SimplexCategory.mk 0)) v))
local notation "p" => weightedIndDensityIndexProjection F
local notation "H" => weightedIndDensityRelativeDiagram κ F hF

/-- 同じ大域分類族の native な全余錐の左制限は同値。 -/
lemma weightedIndDensityRelativeDiagram_nativeRestriction_isQCatEquivalence :
    IsQCatEquivalence (sliceUnderRestrict H (relativeJoinInl p (𝟙 _))) := by
  letI := uliftWeightedRightFibrationProjection_cocartesian F
  exact sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H _
    (F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H
      (weightedIndDensityRelativeDiagram_allFibers_isColimit κ F hF))

/-- 同じ全図式の左 Kan 像についても native な全余錐の左制限は同値。 -/
lemma weightedIndDensityRelativeDiagram_image_nativeRestriction_isQCatEquivalence
    [∀ i, IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    IsQCatEquivalence (sliceUnderRestrict (H ≫ G) (relativeJoinInl p (𝟙 _))) := by
  letI := uliftWeightedRightFibrationProjection_cocartesian F
  exact sliceUnderRestrict_isQCatEquivalence_of_initialBoundary (H ≫ G) _
    (F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p (H ≫ G)
      (weightedIndDensityRelativeDiagram_allFibers_image_isColimit κ F hF β hβ))

end SerrePositivity.InfinityCategories.F2.Ind
