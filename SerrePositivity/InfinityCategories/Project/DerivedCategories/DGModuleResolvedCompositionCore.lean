module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedPrecompCompositionEq
/-!
概要：実分解圏上の指定三比較の経路を構成する。
方針：元の両射影と同じ augmentation 比較を保ち、入力切断前の経路を明示する。
規約：元の合成子の定義を変更しない。使われ方：raw factor と augmentation による計算。
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
/-- 入力切断を前合成する前の、元の指定三比較の全関手経路。 -/
def dgModuleResolvedCompositionCoreIso
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
          ((_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C K (F.comp H)) := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F
  let I := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F
  have hc₀ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).comp H = G.comp (I.comp H) := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource, EnrichedFunctor.comp_map,
      Category.assoc, eqToHom_refl, Category.comp_id]
  have hc₁ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).comp H = P.comp (F.comp H) := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget, EnrichedFunctor.comp_map,
      Category.assoc, eqToHom_refl, Category.comp_id]
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationResolvedComparisonIso R C E K F H hq
  rw [hc₀, hc₁] at e
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K (I.comp H))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C K (F.comp H)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K G
    (I.comp H)).symm ≪≫ e ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R T C K P (F.comp H)
  exact a
end SerrePositivity.InfinityCategories.Project.DerivedCategories
