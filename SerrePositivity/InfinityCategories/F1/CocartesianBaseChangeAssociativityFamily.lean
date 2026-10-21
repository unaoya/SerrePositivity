module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityDiagramComparison
public import SerrePositivity.InfinityCategories.F1.CoreEnrichedComposition
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeJointComparisonEndpoints

/-!
概要：同じ結合比較を、底全体と全 fibration の Cat∞ 値図式の族へ実現する。
方針：元の積上の豊穣比較を実現し、両端を同じ分類主写像へ正規化する。
規約：二回の元の底変換関手と直接の底変換関手そのものを使う。
使われ方：分類 Hom の底変換比較 span の結合の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合比較の、底全体と元の全 fibration の共同の実現。 -/
def cocartesianBaseChangeAssociativityFamily :
    CocartesianFibrationInfinity (nerve C) ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × A))) :=
  (cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram.realization

/-- 零側の同じ全対象・全高次の族は、二回の元の底変換に続く同じ分類主写像。 -/
lemma cocartesianBaseChangeAssociativityFamily_zero :
    cocartesianBaseChangeAssociativityFamily l k ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 0 A)))).app CatInfinity.{u} =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianFibrationInfinityBaseChange (nerveMap l) ≫
          cocartesianStraighteningCoherentMap A := by
  rw [cocartesianBaseChangeAssociativityFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_zero,
    QuasicategoryEnrichedDiagram.realization_precompose, quasicategoryCoreEnrichedFunctor_comp]
  have h := coherentNerveMap_comp
    (cocartesianFibrationBaseChangeCoreEnriched (nerveMap k))
    (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l))
  have h' := congrArg (fun m ↦ m ≫ (cocartesianStrictTransportEnrichedDiagram A).realization) h
  simpa only [Category.assoc, cocartesianStrictTransportEnrichedDiagram_realization,
    cocartesianFibrationInfinityBaseChange, cocartesianFibrationBaseChangeCoreEnriched] using h'

/-- 一側の同じ全対象・全高次の族は、直接の元の底変換に続く同じ分類主写像。 -/
lemma cocartesianBaseChangeAssociativityFamily_one :
    cocartesianBaseChangeAssociativityFamily l k ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex 1 A)))).app CatInfinity.{u} =
      cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
        cocartesianStraighteningCoherentMap A := by
  rw [cocartesianBaseChangeAssociativityFamily, QuasicategoryEnrichedDiagram.realization_reindex,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_one,
    QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianStrictTransportEnrichedDiagram_realization]
  rfl

end SerrePositivity.InfinityCategories
