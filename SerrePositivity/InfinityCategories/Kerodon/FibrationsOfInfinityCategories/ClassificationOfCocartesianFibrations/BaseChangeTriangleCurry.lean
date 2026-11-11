module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeTriangleFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeTriangleComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramTriangleCurry

/-!
概要：元の底変換三角形を関手空間内の同じ二単体族へ移す。
方針：元の全体の共同実現を curry し、三面を元の比較の区間族へ厳密に戻す。
規約：長辺は既存の直接の底変換比較 span に使う同じ区間族。
使われ方：元の Hom 比較 span の合成と Segal 制限の整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ底変換三角形の、元の全 fibration の関手空間内の二単体族。 -/
def cocartesianBaseChangeTriangleCurryFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C) ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTriangleFamily l k ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramSimplexCurry 2 A

/-- 同じ三角形の最初の面は、元の最初の比較を底で制限した同じ区間族。 -/
lemma cocartesianBaseChangeTriangleCurryFamily_first :
    cocartesianBaseChangeTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (2 : Fin 3))).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l).arrowDiagram.realization ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry A := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangleCurry_first
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k))

/-- 同じ三角形の次の面は、元の二回目の比較と結合比較を合成した同じ区間族。 -/
lemma cocartesianBaseChangeTriangleCurryFamily_second :
    cocartesianBaseChangeTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (0 : Fin 3))).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k)).arrowDiagram.realization ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry A := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangleCurry_second
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k))

/-- 同じ三角形の長辺は、既存の直接の底変換比較の元の区間族そのもの。 -/
lemma cocartesianBaseChangeTriangleCurryFamily_long :
    cocartesianBaseChangeTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (1 : Fin 3))).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointIntervalFamily (l ⋙ k) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangleCurry_long
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTriangle_comparison] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
