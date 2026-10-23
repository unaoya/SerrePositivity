module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NerveStructure
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! native 加群 dg nerve を共通標的とする F2 の実 lax pullback への比較写像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

def dgGluingAugmentationArrowFamily :
    dgNerve R (DGGluingObject R C D M) ⟶
      (ihom (Δ[1] : SSet)).obj (dgNerve R (RightModule R C)) :=
  curry ((β_ (Δ[1] : SSet) (dgNerve R (DGGluingObject R C D M))).hom ≫
    (dgGluingAugmentationNerveHomotopy R C D M).h)

lemma dgGluingAugmentationArrowFamily_source :
    dgGluingAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    dgGluingLeftNerve R C D M ≫ dgNerve.map (dgYoneda R C) := by
  rw [dgGluingAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingAugmentationNerveHomotopy R C D M).h₀

lemma dgGluingAugmentationArrowFamily_target :
    dgGluingAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
    dgGluingRightNerve R C D M ≫ dgNerve.map M.toFunctor := by
  rw [dgGluingAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingAugmentationNerveHomotopy R C D M).h₁

/-- 元の二射影と augmentation 全単体族を保持する実比較。 -/
def dgGluingNerveLaxComparison : dgNerve R (DGGluingObject R C D M) ⟶
    F2.laxPullback (dgNerve.map (dgYoneda R C)) (dgNerve.map M.toFunctor) :=
  F2.laxPullbackLift _ _ (dgGluingLeftNerve R C D M) (dgGluingRightNerve R C D M)
    (dgGluingAugmentationArrowFamily R C D M)
    (dgGluingAugmentationArrowFamily_source R C D M)
    (dgGluingAugmentationArrowFamily_target R C D M)

lemma dgGluingNerveLaxComparison_fst :
    dgGluingNerveLaxComparison R C D M ≫
      F2.laxPullbackFst (dgNerve.map (dgYoneda R C)) (dgNerve.map M.toFunctor) =
    dgGluingLeftNerve R C D M := F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingNerveLaxComparison_snd :
    dgGluingNerveLaxComparison R C D M ≫
      F2.laxPullbackSnd (dgNerve.map (dgYoneda R C)) (dgNerve.map M.toFunctor) =
    dgGluingRightNerve R C D M := F2.laxPullbackLift_snd _ _ _ _ _ _ _

lemma dgGluingNerveLaxComparison_arrow :
    dgGluingNerveLaxComparison R C D M ≫
      F2.laxPullbackArrow (dgNerve.map (dgYoneda R C)) (dgNerve.map M.toFunctor) =
    dgGluingAugmentationArrowFamily R C D M := F2.laxPullbackLift_arrow _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
