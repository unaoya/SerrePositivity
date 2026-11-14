module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationHomTargetSpace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleResolvedAugmentationProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGFullSubcategoryHomTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomTargetSpaceComparison
/-!
概要：元の実導来関手の Hom 試験を、生の入力像の同じ Hom 試験へ全関手同型で比較する。
方針：同じ augmentation の空間値同型を実入力切断に戻し、充満部分圏と F1 へ照合する。
規約：生の出力の射影性も入力の Small 性も不要。使われ方：一般 kernel の有限極限保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedHomTargetSpaceIso
    (T : _root_.SerrePositivity.DifferentialGraded.RightModule R E)
    (hT : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) T)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomTargetSpaceIso R C E F T hT).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map S)
  simp only [← Category.assoc, ← Functor.map_comp] at e
  dsimp only [S] at e
  simp only [Category.assoc] at e
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSection_augmentationSource, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSection_augmentationTarget] at e
  exact e
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedRepresentableHomSpaceIso (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T.val) := by
  have e := dgModuleResolvedHomTargetSpaceIso R C E F T.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R E T)
  simpa only [Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryHomTargetUnderlyingSpaceInfinity] using! e
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedF1HomSpaceIso (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T))
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T.val)) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetSpaceComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) T).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F))).symm ≪≫
    dgModuleResolvedRepresentableHomSpaceIso R C E F T ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetSpaceComparisonIso R (RightModule R E) T.val).precomp
        ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
