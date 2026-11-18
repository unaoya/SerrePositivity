module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramRows
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramDiagonalMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TripleSimplicialDiagonal
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicialColumnWeak

/-!
# 元の単体的二方向図式の射列長を固定した部分対角

概要：元の全圏の対角比較を、固定射列長ごとの元の部分対角の弱比較へ還元する。
方針：三重対角の元の同型と列の弱同値による対角判定を使う。
規約：底や係数の各通常次数での弱同値性は要求しない。
使われ方：DK10.6(ii)の固定対象列ごとの Hom 因子による判定。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories

variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u})

def partialRows : SimplicialObject SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.partialDiagonalFunctor.obj (D ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rowsFunctor)

def partialRowsIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRows D) ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBar D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fullDiagonalIso (D ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rowsFunctor)

def chainRow (n : SimplexCategoryᵒᵖ) : SSet.{u} := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRows D).flip.obj n

variable {D} {E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} (τ : D ⟶ E)

def partialRowsMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRows D ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRows E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.partialDiagonalFunctor.map (Functor.whiskerRight τ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rowsFunctor)

def chainRowMap (n : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRow D n ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRow E n :=
  ((flipFunctor _ _ _).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsMap τ)).app n

lemma partialRowsIso_naturality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsMap τ) ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsIso E).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsIso D).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalBarMap τ := by
  ext n e
  rfl

lemma diagonalTotalMap_weak_of_chainRows
    (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRowMap τ n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalTotalMap τ) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.diagonalMap_weak_iff τ).mpr
  have hc := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak_of_columns
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsMap τ) h).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsIso E)).isWeakHomotopyEquivalence
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsIso_naturality τ] at hc
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.partialRowsIso D)).isWeakHomotopyEquivalence
  exact hd.cancel_left hc

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
