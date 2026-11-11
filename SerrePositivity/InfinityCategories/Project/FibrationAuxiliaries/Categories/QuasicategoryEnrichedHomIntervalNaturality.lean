module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedHomInterval
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramReindexRealization
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramPrecomposeRealization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedHomIntervalNaturality

/-!
概要：同じ全 Hom の区間作用は、底の制限と豊穣前合成に厳密に自然。
方針：同じ prism を展開し、共同実現と coherent Hom の自然性を使う。
規約：比較作用そのものの可換式であり、独立な Hom の同値へ置き換えない。
使われ方：元の分類 Hom 比較のセル制限による降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

local instance quasicategoryHomNaturality_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 同じ全 Hom の区間作用は、底の添字の同じ制限と厳密に可換。 -/
lemma quasicategoryEnrichedDiagramHomInterval_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (k : K ⥤ J)
    (X Y : TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval (D.reindex k) X Y =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval D X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve
            (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor (D.toCoreEnrichedFunctor.obj X)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve
            (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor (D.toCoreEnrichedFunctor.obj Y))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_uncurry, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval_uncurry, ← D.realization_reindex k]
  simp only [Category.assoc]

/-- 同じ全 Hom の区間作用は、始域の同じ豊穣 Hom 作用での前合成を回収する。 -/
lemma quasicategoryEnrichedDiagramHomInterval_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (R : EnrichedFunctor SSet.{u} L C)
    (X Y : TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} L) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval (D.precompose R) X Y =
      (SSet.uliftFunctor.{u + 1, u}).map ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R).map X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval D
          ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R).obj X)
          ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R).obj Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramHomInterval_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.realization_precompose]
  have h := congrArg (fun f ↦ f ≫ D.realization)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.coherentRightHomInterval_enriched_naturality (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R) X Y)
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
