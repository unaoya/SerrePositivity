module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedNerveStructure
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! β5 の導来加群 ∞ 圏を共通標的とする F2 の実 lax pullback への比較写像。 -/
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

def dgGluingDerivedAugmentationArrowFamily :
    dgNerve R (DGGluingObject R C D M) ⟶
      (ihom (Δ[1] : SSet)).obj (dgModuleDerivedInfinityCategory R C) :=
  curry ((β_ (Δ[1] : SSet) (dgNerve R (DGGluingObject R C D M))).hom ≫
    (dgGluingDerivedAugmentationHomotopy R C D M).h)

lemma dgGluingDerivedAugmentationArrowFamily_source :
    dgGluingDerivedAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    dgGluingLeftNerve R C D M ≫ dgGluingDerivedYoneda R C := by
  rw [dgGluingDerivedAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingDerivedAugmentationHomotopy R C D M).h₀

lemma dgGluingDerivedAugmentationArrowFamily_target :
    dgGluingDerivedAugmentationArrowFamily R C D M ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
    dgGluingRightNerve R C D M ≫ dgGluingDerivedCoefficient R C D M := by
  rw [dgGluingDerivedAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingDerivedAugmentationHomotopy R C D M).h₁

/-- 元の二射影と augmentation 全単体族を保持する実比較。 -/
def dgGluingDerivedNerveLaxComparison : dgNerve R (DGGluingObject R C D M) ⟶
    F2.laxPullback (dgGluingDerivedYoneda R C) (dgGluingDerivedCoefficient R C D M) :=
  F2.laxPullbackLift _ _ (dgGluingLeftNerve R C D M) (dgGluingRightNerve R C D M)
    (dgGluingDerivedAugmentationArrowFamily R C D M)
    (dgGluingDerivedAugmentationArrowFamily_source R C D M)
    (dgGluingDerivedAugmentationArrowFamily_target R C D M)

lemma dgGluingDerivedNerveLaxComparison_fst :
    dgGluingDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackFst (dgGluingDerivedYoneda R C) (dgGluingDerivedCoefficient R C D M) =
    dgGluingLeftNerve R C D M := F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingDerivedNerveLaxComparison_snd :
    dgGluingDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackSnd (dgGluingDerivedYoneda R C) (dgGluingDerivedCoefficient R C D M) =
    dgGluingRightNerve R C D M := F2.laxPullbackLift_snd _ _ _ _ _ _ _

lemma dgGluingDerivedNerveLaxComparison_arrow :
    dgGluingDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackArrow (dgGluingDerivedYoneda R C) (dgGluingDerivedCoefficient R C D M) =
    dgGluingDerivedAugmentationArrowFamily R C D M := F2.laxPullbackLift_arrow _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
