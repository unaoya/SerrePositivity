module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramDiagonal

/-!
# 元の単体的二方向比較射の対角での自然性

概要：底と両係数の元の自然変換による対角の比較を同じ射で照合する。
方針：元の各次数の Thomason 正方形を同じ対角へ移す。
規約：元の全圏と bar の対角射の弱同値性は同値であり、入力へ移さない。
使われ方：DK10.4–10.6の係数・底の弱不変性の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories

variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} (τ : D ⟶ E)

def diagonalBarMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBar D ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBar E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight τ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.barFunctor)

def diagonalTotalMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalTotalNerve D ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalTotalNerve E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
    (Functor.whiskerRight τ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.totalFunctor ⋙ nerveFunctor))

lemma diagonalThomasonMap_naturality :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap D ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalTotalMap τ =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBarMap τ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap E := by
  ext n e
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.thomasonMap.naturality (τ.app n)).symm n) e

lemma diagonalMap_weak_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalTotalMap τ) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBarMap τ) := by
  constructor
  · intro h
    have hc := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_isWeakHomotopyEquivalence D).comp h
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_naturality τ] at hc
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_isWeakHomotopyEquivalence E).cancel_right hc
  · intro h
    have hc := h.comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_isWeakHomotopyEquivalence E)
    rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_naturality τ] at hc
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalThomasonMap_isWeakHomotopyEquivalence D).cancel_left hc

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
