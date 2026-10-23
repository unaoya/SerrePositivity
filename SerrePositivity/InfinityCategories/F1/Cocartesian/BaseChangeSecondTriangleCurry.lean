module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramArrowPrecompose
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleCurry
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityEdge

/-!
概要：元の第二比較を、二回目の底変換比較と同じ結合比較の三角形へ分解する。
方針：同じ二つの豊穣比較の三角形を共同実現し、元の三つの区間族を回収する。
規約：元の全 fibration と元の全 Hom で自然な同じ比較。
使われ方：既存の元の Hom 輸送の合成と Segal 制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の二回目の底変換比較の区間族は、既存の比較の元の底変換による前合成。 -/
lemma cocartesianBaseChangeJointIntervalFamily_precompose :
    ((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k))).arrowDiagram.realization ≫
        qCatDiagramArrowCurry A =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianBaseChangeJointIntervalFamily l := by
  rw [QuasicategoryEnrichedDiagramComparison.arrowDiagram_precompose,
    QuasicategoryEnrichedDiagram.realization_precompose, Category.assoc]
  rfl

/-- 二回目の元の比較と元の結合比較を三辺に持つ、同じ全高次の二単体族。 -/
def cocartesianBaseChangeSecondTriangleCurryFamily :
    CocartesianFibrationInfinity (nerve C) ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  quasicategoryEnrichedDiagramTriangleCurry
    ((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k)))
    (cocartesianBaseChangeAssociativityDiagramComparison l k)

/-- 同じ三角形の最初の辺は、既存の二回目の比較の同じ前合成族。 -/
lemma cocartesianBaseChangeSecondTriangleCurryFamily_first :
    cocartesianBaseChangeSecondTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (2 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianBaseChangeJointIntervalFamily l := by
  rw [cocartesianBaseChangeSecondTriangleCurryFamily,
    quasicategoryEnrichedDiagramTriangleCurry_first,
    cocartesianBaseChangeJointIntervalFamily_precompose]

/-- 同じ三角形の次の辺は、既存の元の結合比較の区間族そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleCurryFamily_second :
    cocartesianBaseChangeSecondTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (0 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
      cocartesianBaseChangeAssociativityIntervalFamily l k :=
  quasicategoryEnrichedDiagramTriangleCurry_second _ _

/-- 同じ三角形の長辺は、元の比較三角形の第二面の同じ区間族。 -/
lemma cocartesianBaseChangeSecondTriangleCurryFamily_long :
    cocartesianBaseChangeSecondTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (1 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
      cocartesianBaseChangeTriangleCurryFamily l k ≫
        (pre (stdSimplex.δ (0 : Fin 3))).app
          (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) := by
  rw [cocartesianBaseChangeSecondTriangleCurryFamily,
    quasicategoryEnrichedDiagramTriangleCurry_long, cocartesianBaseChangeTriangleCurryFamily_second]

end SerrePositivity.InfinityCategories
