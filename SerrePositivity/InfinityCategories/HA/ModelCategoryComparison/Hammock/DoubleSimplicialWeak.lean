module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-!
# 元の二重単体集合の行ごとの弱同値から対角の弱同値へ

概要：元の全行の弱同値は元の対角写像自身の弱同値を与える。
方針：元の弱同値を anodyne 局所化へ移し、既存のモデル不要の対角定理を使う。
規約：元の対角関手を保持し、単体集合モデル構造を入力しない。
使われ方：DK 命題2.2の元の対角の右比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

lemma diagonalFunctor_map_weak {B D : SimplicialObject SSet.{u}} (f : B ⟶ D)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f.app n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  change IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.BisimplicialModel.diagonal.map f))
  exact _root_.SerrePositivity.BisimplicialModel.localized_diagonal_map f
    (fun n => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (f.app n) (hf n))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial
