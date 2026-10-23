module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismNativeCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryTipReflection

/-!
概要：補間全族の元の試験族への制限は、同じ元の q と実 comma 内で同型。
方針：両全余錐の厳密な回収と、両固定境界の比較の全族への反映を合成する。
規約：Yoneda の充填性を仮定しない。使われ方：同じ元の q への余錐の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 元の補間族の制限を、同じ元の q の全変換族へ実 comma 内の同型で戻す。 -/
lemma nonempty_indArrowInterpolationOldFamily_iso :
    Nonempty (FunctorIso (indArrowInterpolationOldFamily V) q) := by
  let p := SSet.yonedaEquiv.symm (functorVertex (liftedIntervalToSmall ≫ D)) ≫
    arrowDiagramUniverseRestriction (IndInfinity κ C)
  let b := curry ((β_ (Δ[1] : SSet.{u + 1})
    ((SSet.uliftFunctor.{u + 1, u}).obj A)).hom ≫
      indArrowOriginalFamily κ D q ≫ indYoneda κ C) ≫
        arrowDiagramUniverseRestriction (IndInfinity κ C)
  have hp : p = SSet.yonedaEquiv.symm (functorVertex D) :=
    indArrowNormalizedPrism_curry_tip κ D
  refine nonempty_commaFunctorIso_of_fixedCoconeBoundaryIso_of_tip_eq
    p (SSet.yonedaEquiv.symm (functorVertex D)) hp b (diagramYoneda κ (Δ[1] : SSet.{u}) C)
    (diagramYoneda_isFullyFaithful κ Δ[1] C) (indArrowInterpolationOldFamily V) q
    (indArrowPrismNativeReconstructedVertex V.slicePrism)
    (indArrowPrismNativeOriginalVertex V.slicePrism) ?_ ?_
    (indArrowPrismNativeBoundaryIso V.slicePrism)
  · exact (indArrowPrismNativeReconstructedVertex_val V.slicePrism).trans
      (congrArg functorVertex (indArrowInterpolationOldFamily_uncurry V).symm)
  · exact (indArrowPrismNativeOriginalVertex_val V.slicePrism).trans
      (congrArg functorVertex (diagramCommaSliceProjection_uncurry q).symm)

end SerrePositivity.InfinityCategories.F2.Ind
