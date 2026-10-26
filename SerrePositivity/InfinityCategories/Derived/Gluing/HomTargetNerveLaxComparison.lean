module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNerveStructure
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
/-!
概要：元共通終域を基底とする lax pullback への Hom gluing の実比較。
方針：元終域の augmentation 全族を curry し、元二射影とともに実 pullback へ入れる。
規約：比較写像の構成であり、同値性や cone 差との全比較は別途証明する。
使われ方：元二脚・恒等二脚の比較と、その全 cone 自然性の始点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded DGNerve
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => DGGluingObject R C D M

def dgGluingHomTargetAugmentationArrowFamily :
    dgNerve R G ⟶ (ihom (Δ[1] : SSet)).obj (dgNerve R E) :=
  curry ((β_ (Δ[1] : SSet) (dgNerve R G)).hom ≫
    (dgGluingHomTargetAugmentationHomotopy R C D E p q).h)

lemma dgGluingHomTargetAugmentationArrowFamily_source :
    dgGluingHomTargetAugmentationArrowFamily R C D E p q ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    dgNerve.map (dgGluingLeft R C D M) ≫ dgNerve.map p := by
  rw [dgGluingHomTargetAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingHomTargetAugmentationHomotopy R C D E p q).h₀

lemma dgGluingHomTargetAugmentationArrowFamily_target :
    dgGluingHomTargetAugmentationArrowFamily R C D E p q ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
    dgNerve.map (dgGluingRight R C D M) ≫ dgNerve.map q := by
  rw [dgGluingHomTargetAugmentationArrowFamily, curry_evaluateFunctorAt_interval]
  exact (dgGluingHomTargetAugmentationHomotopy R C D E p q).h₁

/-- 元二射影と元終域内の比較辺全族を保持する指定比較。 -/
def dgGluingHomTargetNerveLaxComparison :
    dgNerve R G ⟶ F2.laxPullback (dgNerve.map p) (dgNerve.map q) :=
  F2.laxPullbackLift _ _ (dgNerve.map (dgGluingLeft R C D M))
    (dgNerve.map (dgGluingRight R C D M))
    (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
    (dgGluingHomTargetAugmentationArrowFamily_source R C D E p q)
    (dgGluingHomTargetAugmentationArrowFamily_target R C D E p q)

lemma dgGluingHomTargetNerveLaxComparison_fst :
    dgGluingHomTargetNerveLaxComparison R C D E p q ≫
      F2.laxPullbackFst (dgNerve.map p) (dgNerve.map q) =
    dgNerve.map (dgGluingLeft R C D M) := F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingHomTargetNerveLaxComparison_snd :
    dgGluingHomTargetNerveLaxComparison R C D E p q ≫
      F2.laxPullbackSnd (dgNerve.map p) (dgNerve.map q) =
    dgNerve.map (dgGluingRight R C D M) := F2.laxPullbackLift_snd _ _ _ _ _ _ _

lemma dgGluingHomTargetNerveLaxComparison_arrow :
    dgGluingHomTargetNerveLaxComparison R C D E p q ≫
      F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q) =
    dgGluingHomTargetAugmentationArrowFamily R C D E p q :=
  F2.laxPullbackLift_arrow _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
