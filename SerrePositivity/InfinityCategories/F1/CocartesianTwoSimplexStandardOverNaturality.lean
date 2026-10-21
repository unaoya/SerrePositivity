module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexStandardOverIsos
public import SerrePositivity.InfinityCategories.F1.UniverseRelativeOverPre

/-!
概要：元の共有頂点の表示同型は、標準二辺への同じ二包含に整合する。
方針：底上の射の二つの等式を元の単体の面の射へ還元する。
規約：同じ二辺と共有頂点を保持する。
使われ方：元の target pullback と標準内ホーンの target pullback の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)

/-- 同じ共有頂点の同型は、最初の辺の終点への包含と底上で可換。 -/
lemma cocartesianTwoSimplexStandardOverIso_first :
    (cocartesianTwoSimplexStandardSharedOverIso k).hom ≫
      uliftOverMorphism (cocartesianTwoSimplexSharedToFirst k) =
    InnerTwoHornOver.toFirst (cocartesianTwoSimplexStandardHorn k) ≫
      (cocartesianTwoSimplexStandardFirstOverIso k).hom := by
  apply (Over.forget _).map_injective
  change (localKanDiagramBaseIso.{u} 0).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))) =
    stdSimplex.δ (0 : Fin 2) ≫ (localKanDiagramBaseIso.{u} 1).hom
  exact cocartesianSimplexCellIndex_large_projection _

/-- 同じ共有頂点の同型は、次の辺の始点への包含とも底上で可換。 -/
lemma cocartesianTwoSimplexStandardOverIso_second :
    (cocartesianTwoSimplexStandardSharedOverIso k).hom ≫
      uliftOverMorphism (cocartesianTwoSimplexSharedToSecond k) =
    InnerTwoHornOver.toSecond (cocartesianTwoSimplexStandardHorn k) ≫
      (cocartesianTwoSimplexStandardSecondOverIso k).hom := by
  apply (Over.forget _).map_injective
  change (localKanDiagramBaseIso.{u} 0).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))) =
    stdSimplex.δ (1 : Fin 2) ≫ (localKanDiagramBaseIso.{u} 1).hom
  exact cocartesianSimplexCellIndex_large_projection _

end SerrePositivity.InfinityCategories
