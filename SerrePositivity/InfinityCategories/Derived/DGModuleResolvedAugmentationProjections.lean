module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationUnlifted
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
/-!
概要：同じ実入力切断に沿う augmentation の両端を、元の分解関手と入力像へ同定する。
方針：同じ閉辺・coslice 輸送と実入力切断の厳密等式を使う。
規約：生の出力の射影性は不要。使われ方：一般 kernel の完全性の Hom 試験。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ augmentation による全単体的な Hom 比較。 -/
lemma dgModuleResolvedSection_augmentationSource :
    dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
        dgNerve.map (dgModuleAugmentationSource R C E F) =
    dgModuleResolvedInfinity R C E F ≫
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) := by
  have h := congrArg (fun f =>
    dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫ f ≫
      dgNerve.map (dgUniverseLiftDown R (RightModule R E)))
    (dgModuleOutputResolution_replacement R C E F)
  have h1 := congrArg (fun H => dgNerve.map H)
    (dgModuleAugmentationSourceLift_down R C E F)
  have h2 := congrArg (fun H => dgNerve.map H) (dgModuleOutputInclusionLift_down R E)
  simp only [dgNerve.map_comp, Category.assoc] at h h1 h2
  rw [h1, h2] at h
  simpa only [dgModuleResolvedInfinity, Category.assoc] using h
/-- 同じ augmentation による全単体的な Hom 比較。 -/
lemma dgModuleResolvedSection_augmentationTarget :
    dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
        dgNerve.map (dgModuleAugmentationTarget R C E F) = dgNerve.map F := by
  have h := congrArg (fun f =>
    dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫ f ≫
      dgNerve.map (dgUniverseLiftDown R (RightModule R E)))
    (dgModuleOutputResolution_original R C E F)
  have h1 := congrArg (fun H => dgNerve.map H)
    (dgModuleAugmentationTargetLift_down R C E F)
  have h2 := congrArg (fun H => dgNerve.map H) (dgModuleOutputOriginalLift_up_down R C E F)
  simp only [dgNerve.map_comp, Category.assoc] at h h1 h2
  rw [h1, h2] at h
  exact h
end SerrePositivity.InfinityCategories
