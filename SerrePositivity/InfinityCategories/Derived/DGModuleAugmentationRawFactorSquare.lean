module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactor
/-!
概要：元の augmentation の resolved 比較と、同じ raw factor 比較の正方形が可換。
方針：元の raw factor の入力自然性を書き換え、指定前合成比較とその逆を相殺する。
規約：全関手同型の等式。使われ方：元の指定導来合成子の計算式。
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
/-- 同じ指定 raw factor の端点輸送を明示すると、元の augmentation 比較の正方形は可換。 -/
lemma dgModuleAugmentationResolvedComparisonIso_rawFactor
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    dgModuleAugmentationResolvedComparisonIso R C E K F H hq ≪≫
      F2.functorIsoOfEq
        (dgModuleResolvedInfinity_rawFactorIso R (DGModuleFunctorResolutionObject R C E F) K
          ((dgModuleAugmentationTarget R C E F).comp H)) rfl
        (congrArg (fun m => m ≫ dgModuleResolvedInfinity R (RightModule R K) K
          (DGFunctor.id (RightModule R K)))
          (dgNerve.map_comp (dgModuleAugmentationTarget R C E F) H)) =
      F2.functorIsoOfEq
        (dgModuleResolvedInfinity_rawFactorIso R (DGModuleFunctorResolutionObject R C E F) K
          ((dgModuleAugmentationSource R C E F).comp H)) rfl
        (congrArg (fun m => m ≫ dgModuleResolvedInfinity R (RightModule R K) K
          (DGFunctor.id (RightModule R K)))
          (dgNerve.map_comp (dgModuleAugmentationSource R C E F) H)) ≪≫
        dgModuleAugmentationRawFactorIso R C E K F H hq := by
  rw [dgModuleResolvedInfinity_rawFactorIso_precomp,
    dgModuleResolvedInfinity_rawFactorIso_precomp]
  unfold dgModuleAugmentationResolvedComparisonIso dgModuleAugmentationRawFactorIso
    functorIsoPostcompConjugate
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
end SerrePositivity.InfinityCategories
