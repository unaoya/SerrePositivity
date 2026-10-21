module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportInfinity
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportEnrichedRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramArrowEndpoints
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramReindexRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramPrecomposeRealization

/-!
概要：全局所 Hom に自然な同型比較を、底全体と指定同型の ∞ 圏にわたる coherent な族へ実現する。
方針：同じ arrow 図式を実現し、両端を元の分類主写像への合成へ戻す。
規約：元の全 Hom と同じ始域評価・結合共役の作用を保持する。
使われ方：同じ結合 Hom span の全局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 始域の元の全相対 Hom の core を、そのまま元の fibration の ∞ 圏へ評価する。 -/
def cocartesianIsoTransportSource (A : Type u) [Category.{u} A] :
    CocartesianIsoTransportInfinity A ⟶ CocartesianFibrationInfinity (nerve A) :=
  coherentNerveMap (quasicategoryCoreEnrichedFunctor
    (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A))))

/-- 同じ指定同型による全局所 Hom の結合共役を、元の fibration の ∞ 圏へ実現する。 -/
def cocartesianIsoTransportTarget (A : Type u) [Category.{u} A] :
    CocartesianIsoTransportInfinity A ⟶ CocartesianFibrationInfinity (nerve A) :=
  coherentNerveMap (quasicategoryCoreEnrichedFunctor
    (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A))))

/-- 底全体と元の全局所 Hom に自然な、同じ指定同型の coherent な比較の族。 -/
def cocartesianIsoTransportFamily (A : Type u) [Category.{u} A] :
    CocartesianIsoTransportInfinity A ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × A))) :=
  (cocartesianIsoTransportDiagramComparison A).arrowDiagram.realization

/-- 同じ全局所比較の零端点は、元の始域評価に続く同じ分類主写像。 -/
lemma cocartesianIsoTransportFamily_zero (A : Type u) [Category.{u} A] :
    cocartesianIsoTransportFamily A ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 0 A)))).app CatInfinity.{u} =
    cocartesianIsoTransportSource A ≫ cocartesianStraighteningCoherentMap A := by
  rw [cocartesianIsoTransportFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_zero,
    QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianStrictTransportEnrichedDiagram_realization]
  rfl

/-- 同じ全局所比較の一端点は、元の結合共役に続く同じ分類主写像。 -/
lemma cocartesianIsoTransportFamily_one (A : Type u) [Category.{u} A] :
    cocartesianIsoTransportFamily A ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 1 A)))).app CatInfinity.{u} =
    cocartesianIsoTransportTarget A ≫ cocartesianStraighteningCoherentMap A := by
  rw [cocartesianIsoTransportFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_one,
    QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianStrictTransportEnrichedDiagram_realization]
  rfl

end SerrePositivity.InfinityCategories
