module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CanonicalCoefficientRelativePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyTriangleFillingCriterion
/-! # 六片の実係数対角辺と指定係数辺の相対移送

概要：六片の実係数対角辺を指定した端点で保持し、指定係数辺と同じ関手圏の類へ移す。
方針：明示 prism を保つ実変形を使い、両端固定正規化の辺の類を適用する。
規約：実二単体の対角辺の代表を保持し、主境界の指定辺を変更しない。
使われ方：単位面を消去した高次合成等式を正本の指定三辺の充填へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

lemma dgGluingModelUnitCapTriangleDiagram_coefficient_homotopy :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram R C D M X Y 4 =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationDiagonalHomotopy_h,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCanonicalAugmentationIntervalPrism]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_coefficient_diagonal R C D M X Y

def dgGluingModelUnitCapCoefficientEdge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y)

lemma dgGluingModelUnitCapCoefficientEdge_edge :
    (dgGluingModelUnitCapCoefficientEdge R C D M X Y).edge =
      SSet.yonedaEquiv
        (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram R C D M X Y 4) :=
  congrArg SSet.yonedaEquiv
    (dgGluingModelUnitCapTriangleDiagram_coefficient_homotopy R C D M X Y).symm

lemma dgGluingModelUnitCapCoefficientEdge_class :
    SSet.Truncated.HomotopyCategory.homMk (dgGluingModelUnitCapCoefficientEdge R C D M X Y) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationDiagonalHomotopy_class R C D M X Y

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (dgGluingModelUnitCapCoefficientEdge R C D M X Y) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y))) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y := by
  rw [dgGluingModelUnitCapCoefficientEdge_class R C D M X Y] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleFilling_of_homEq h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
