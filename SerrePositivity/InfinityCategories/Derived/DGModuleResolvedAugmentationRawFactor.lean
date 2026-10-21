module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionRawFactor
/-!
概要：入力切断上の augmentation の通常後続像の端点を、元の分解関手で揃える。
方針：同じ実切断と射影の厳密な単位関係だけで端点を輸送する。
規約：同じ指定比較の値を保つ。使われ方：元の合成子の同じ型での計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 同じ入力切断上の通常後続像を、元の分解関手と通常合成の端点で表す指定同型。 -/
def dgModuleResolvedAugmentationRawFactorIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgModuleResolvedInfinity R C E F ≫
        dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H) ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (dgNerve.map (F.comp H) ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let G := dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  have hs : dgModuleResolvedInfinity R C E F = S ≫ G := by
    simpa only [S, G, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hsp : S ≫ P = 𝟙 _ := dgModuleResolvedSourceSection_comp_source R C E F
  refine F2.functorIsoOfEq
    ((dgModuleAugmentationRawFactorCoreIso R C E K F H hq).precomp S) ?_ ?_
  · rw [hs, Category.assoc]
  · change S ≫ P ≫ _ = _
    rw [← Category.assoc, hsp, Category.id_comp]
/-- 元の三項経路に現れる通常後続像の値を保持する。 -/
lemma dgModuleResolvedAugmentationRawFactorIso_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleResolvedAugmentationRawFactorIso R C E K F H hq)
      ((dgModuleAugmentationRawFactorCoreIso R C E K F H hq).precomp
        (dgModuleResolvedSourceSectionEquivalence R C E F).hom) := by
  unfold dgModuleResolvedAugmentationRawFactorIso
  exact F2.functorIsoOfEq_heq _ _ _
end SerrePositivity.InfinityCategories
