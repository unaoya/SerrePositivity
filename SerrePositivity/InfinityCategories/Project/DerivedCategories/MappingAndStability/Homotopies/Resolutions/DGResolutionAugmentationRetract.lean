module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGResolvedProjectiveVertex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.DGModuleResolutionLocalization
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
/-!
概要：同じ分解 augmentation の半自由入力制限から、元の円柱を保持した戻り同型を回収する。
方針：各半自由入力の射影性と、実半自由包含の完全充満性を使う。
規約：既存の指定導来単位は変更しない。使われ方：K-flat の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の分解 augmentation を半自由入力に制限し、同じ円柱を保って端点を揃える。 -/
def dgModuleResolutionSemifreeAugmentationHomotopy :
    SSet.Homotopy
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
      ((𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D))) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.dgModuleResolutionAugmentationHomotopy R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
  exact { h := H.h
          h₀ := by simpa only [Category.assoc] using! H.h₀
          h₁ := by simpa only [Category.comp_id, Category.id_comp] using! H.h₁
          rel := H.rel }
/-- 半自由入力上では同じ augmentation の各実頂点辺が可逆。 -/
lemma dgModuleResolutionSemifreeAugmentationHomotopy_vertex_isInvertible
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (dgModuleResolutionSemifreeAugmentationHomotopy R D) x).toTruncated := by
  obtain ⟨M, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).symm.surjective x
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy_projective_vertex_isInvertible
    R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) D (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)) M.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M)
  have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (dgModuleResolutionSemifreeAugmentationHomotopy R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.dgModuleResolutionAugmentationHomotopy R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M.val)).edge := by
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge _ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hh).mpr ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl).mpr hr)
/-- 同じ augmentation の半自由制限から回収した分解の戻り同型。 -/
def dgModuleResolutionAugmentationRetractIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (dgModuleResolutionSemifreeAugmentationHomotopy R D)
      (dgModuleResolutionSemifreeAugmentationHomotopy_vertex_isInvertible R D))
/-- 回収した戻り同型の実包含後の射は、同じ半自由制限円柱の類。 -/
lemma dgModuleResolutionAugmentationRetractIso_postcomp_hom :
    ((dgModuleResolutionAugmentationRetractIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgModuleResolutionSemifreeAugmentationHomotopy R D)) := by
  unfold dgModuleResolutionAugmentationRetractIso
  rw [(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso_postcomp]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
