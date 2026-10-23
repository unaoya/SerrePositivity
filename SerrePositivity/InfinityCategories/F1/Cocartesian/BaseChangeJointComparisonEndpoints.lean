module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeJointComparisonFamily
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportEnrichedRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramArrowEndpoints
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramReindexRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramPrecomposeRealization

/-!
概要：底全体の比較の両端は、元の分類主写像の制限と元の底変換に続く分類主写像。
方針：同じ積上の図式を両端で制限し、実現と制限・前合成の厳密な自然性を使う。
規約：元の全 fibration と全高次の射の等式を証明する。
使われ方：同じ分類主写像の底変換との coherent な比較の両端の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 同じ比較の零端点は、構成済みの元の分類主写像を底で制限した写像。 -/
lemma cocartesianBaseChangeJointComparisonFamily_zero_restriction :
    cocartesianBaseChangeJointComparisonFamily k ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 0 D)))).app CatInfinity.{u} =
    cocartesianStraighteningCoherentMap C ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app CatInfinity.{u} := by
  rw [cocartesianBaseChangeJointComparisonFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_zero,
    ← QuasicategoryEnrichedDiagram.realization_reindex,
    cocartesianStrictTransportEnrichedDiagram_realization]

/-- 同じ比較の一端点は、元の底変換の ∞ 関手に続く元の分類主写像。 -/
lemma cocartesianBaseChangeJointComparisonFamily_one_restriction :
    cocartesianBaseChangeJointComparisonFamily k ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 1 D)))).app CatInfinity.{u} =
    cocartesianFibrationInfinityBaseChange (nerveMap k) ≫ cocartesianStraighteningCoherentMap D := by
  rw [cocartesianBaseChangeJointComparisonFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_one,
    QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianStrictTransportEnrichedDiagram_realization]
  rfl

end SerrePositivity.InfinityCategories
