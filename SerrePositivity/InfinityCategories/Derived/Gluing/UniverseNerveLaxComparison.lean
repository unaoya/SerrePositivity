module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! 任意の対象宇宙の元の gluing 圏から、共通単体宇宙の実 lax pullback への比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C : Type v) [DGCategory R C] [Small.{u} C] (D : Type w) [DGCategory R D]
  (M : Bimodule R C D)

def dgGluingUniverseAugmentationArrowFamily :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj (dgNerve R (DGGluingObject R C D M)) ⟶
      (ihom (Δ[1] : SSet)).obj
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
          (dgNerve R (RightModule R C))) :=
  curry ((β_ (Δ[1] : SSet)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)))).hom ≫
    (dgGluingUniverseAugmentationHomotopy R C D M).h)

lemma dgGluingUniverseAugmentationArrowFamily_source :
    dgGluingUniverseAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseYoneda.{u, v, w} R C := by
  rw [dgGluingUniverseAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingUniverseAugmentationHomotopy R C D M).h₀

lemma dgGluingUniverseAugmentationArrowFamily_target :
    dgGluingUniverseAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
    dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseCoefficient R C D M := by
  rw [dgGluingUniverseAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingUniverseAugmentationHomotopy R C D M).h₁

/-- 元の二射影と augmentation 全単体族を保持する実比較。 -/
def dgGluingUniverseNerveLaxComparison :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) ⟶
    F2.laxPullback (dgGluingUniverseYoneda.{u, v, w} R C) (dgGluingUniverseCoefficient R C D M) :=
  F2.laxPullbackLift _ _ (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M)
    (dgGluingUniverseAugmentationArrowFamily R C D M)
    (dgGluingUniverseAugmentationArrowFamily_source R C D M)
    (dgGluingUniverseAugmentationArrowFamily_target R C D M)

lemma dgGluingUniverseNerveLaxComparison_fst :
    dgGluingUniverseNerveLaxComparison R C D M ≫
      F2.laxPullbackFst (dgGluingUniverseYoneda.{u, v, w} R C)
        (dgGluingUniverseCoefficient R C D M) =
    dgGluingUniverseLeftNerve R C D M := F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingUniverseNerveLaxComparison_snd :
    dgGluingUniverseNerveLaxComparison R C D M ≫
      F2.laxPullbackSnd (dgGluingUniverseYoneda.{u, v, w} R C)
        (dgGluingUniverseCoefficient R C D M) =
    dgGluingUniverseRightNerve R C D M := F2.laxPullbackLift_snd _ _ _ _ _ _ _

lemma dgGluingUniverseNerveLaxComparison_arrow :
    dgGluingUniverseNerveLaxComparison R C D M ≫
      F2.laxPullbackArrow (dgGluingUniverseYoneda.{u, v, w} R C)
        (dgGluingUniverseCoefficient R C D M) =
    dgGluingUniverseAugmentationArrowFamily R C D M := F2.laxPullbackLift_arrow _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
