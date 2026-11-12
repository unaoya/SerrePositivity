module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRealization

/-!
概要：元の豊穣図式の実現は、全 fibration の同じ豊穣関手による前合成と厳密に可換。
方針：元の core 上の全 Hom の作用を比較し、coherent nerve の後合成則へ渡す。
規約：同じ全対象・全高次に関する射の等式。
使われ方：比較の終端を底変換の ∞ 関手に続く元の分類主写像へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

local instance quasicategoryEnrichedPrecompose_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 全対象と全高次 Hom の元の core 上の前合成は、同じ豊穣後合成そのもの。 -/
lemma QuasicategoryEnrichedDiagram.toCoreEnrichedFunctor_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (R : EnrichedFunctor SSet.{u} L C) :
    (D.precompose R).toCoreEnrichedFunctor =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R).comp SSet D.toCoreEnrichedFunctor := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 元の全対象の豊穣な前合成と、その同じ図式の実現は厳密に可換。 -/
lemma QuasicategoryEnrichedDiagram.realization_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (R : EnrichedFunctor SSet.{u} L C) :
    (D.precompose R).realization = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor R) ≫
      D.realization := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.realization, toCoreEnrichedFunctor_precompose, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.realization, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
