module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactorSquare
/-!
概要：同じ augmentation の通常後続像を、実二射影と通常合成の端点へ揃える。
方針：元の二つの dg 射影と nerve 合成の厳密等式だけで端点を輸送する。
規約：元の指定比較の値を保持する。使われ方：指定三項経路の raw factor 計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 同じ augmentation の通常後続像を、実二射影の通常合成による両端へ輸送する。 -/
def dgModuleAugmentationRawFactorCoreIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) ≫
        dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H) ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F) ≫ dgNerve.map (F.comp H) ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  refine F2.functorIsoOfEq (dgModuleAugmentationRawFactorIso R C E K F H hq) ?_ ?_
  · simp only [dgModuleAugmentationSource, dgNerve.map_comp, Category.assoc]
  · simp only [dgModuleAugmentationTarget, dgNerve.map_comp, Category.assoc]
/-- 両射影による端点表示への輸送は、同じ元の指定比較を型付きで保持する。 -/
lemma dgModuleAugmentationRawFactorCoreIso_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleAugmentationRawFactorCoreIso R C E K F H hq)
      (dgModuleAugmentationRawFactorIso R C E K F H hq) := by
  unfold dgModuleAugmentationRawFactorCoreIso
  exact F2.functorIsoOfEq_heq _ _ _
end SerrePositivity.InfinityCategories
