module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedCompositionRawFactor
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E K : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
/-- 同じ入力切断上の通常後続像を、元の分解関手と通常合成の端点で表す指定同型。 -/
def dgModuleResolvedAugmentationRawFactorIso
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  let S := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F)
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F = S ≫ G := by
    simpa only [S, G, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hsp : S ≫ P = 𝟙 _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_comp_source R C E F
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H hq).precomp S) ?_ ?_
  · rw [hs, Category.assoc]
  · change S ≫ P ≫ _ = _
    rw [← Category.assoc, hsp, Category.id_comp]
/-- 元の三項経路に現れる通常後続像の値を保持する。 -/
lemma dgModuleResolvedAugmentationRawFactorIso_heq
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleResolvedAugmentationRawFactorIso R C E K F H hq)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H hq).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).hom) := by
  unfold dgModuleResolvedAugmentationRawFactorIso
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
