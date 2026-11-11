module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRealization

/-!
概要：元の quasicategory 値豊穣図式の実現は、底の添字の制限と厳密に可換。
方針：同じ全高次の対角評価を各単体で比較する。
規約：添字関手の単射性は要求しない。
使われ方：二点と底の積上の比較の両端を元の全図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

local instance quasicategoryEnrichedReindex_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 添字の制限と元の全対象の対角評価は、同じ全高次で厳密に可換。 -/
lemma QuasicategoryEnrichedDiagram.reindex_diagonal
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J L I : Type u} [Category.{u} J] [Category.{u} L] [LinearOrder I]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (k : L ⥤ J) (σ : I ⥤ L)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I)
      (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramEvaluation σ (T.comp SSet (D.reindex k).toCoreEnrichedFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramEvaluation (σ ⋙ k) (T.comp SSet D.toCoreEnrichedFunctor) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom σ
    (T.comp SSet (D.reindex k).toCoreEnrichedFunctor) i j).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom (σ ⋙ k) (T.comp SSet D.toCoreEnrichedFunctor) i j).app n P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le _ _ i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le _ _ i j hij]
  rfl

/-- 任意の底の添字の制限と元の全対象・全高次の実現は、射の等式として可換。 -/
lemma QuasicategoryEnrichedDiagram.realization_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (k : L ⥤ J) :
    D.realization ≫ (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} =
      (D.reindex k).realization := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.realization, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact (D.reindex_diagonal k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramSimplexBase σ.down) T).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
