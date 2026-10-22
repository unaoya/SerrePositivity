module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.F2.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! 任意の対象宇宙の元の gluing 圏から、導来加群 ∞ 圏上の実 lax pullback への比較。 -/
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

def dgGluingUniverseDerivedAugmentationArrowFamily :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj (dgNerve R (DGGluingObject R C D M)) ⟶
      (ihom (Δ[1] : SSet)).obj
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
          (dgModuleDerivedInfinityCategory R C)) :=
  curry ((β_ (Δ[1] : SSet)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)))).hom ≫
    (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h)

lemma dgGluingUniverseDerivedAugmentationArrowFamily_source :
    dgGluingUniverseDerivedAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseDerivedYoneda.{u, v, w} R C := by
  rw [dgGluingUniverseDerivedAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h₀

lemma dgGluingUniverseDerivedAugmentationArrowFamily_target :
    dgGluingUniverseDerivedAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
    dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseDerivedCoefficient R C D M := by
  rw [dgGluingUniverseDerivedAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h₁

/-- 元の二射影と augmentation 全単体族を保持する実比較。 -/
def dgGluingUniverseDerivedNerveLaxComparison :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) ⟶
    F2.laxPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) :=
  F2.laxPullbackLift _ _ (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M)
    (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
    (dgGluingUniverseDerivedAugmentationArrowFamily_source R C D M)
    (dgGluingUniverseDerivedAugmentationArrowFamily_target R C D M)

lemma dgGluingUniverseDerivedNerveLaxComparison_fst :
    dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
    dgGluingUniverseLeftNerve R C D M := F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingUniverseDerivedNerveLaxComparison_snd :
    dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
    dgGluingUniverseRightNerve R C D M := F2.laxPullbackLift_snd _ _ _ _ _ _ _

lemma dgGluingUniverseDerivedNerveLaxComparison_arrow :
    dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
    dgGluingUniverseDerivedAugmentationArrowFamily R C D M := F2.laxPullbackLift_arrow _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
