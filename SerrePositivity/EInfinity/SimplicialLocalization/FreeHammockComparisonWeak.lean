module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionGeneratorPartition
public import SerrePositivity.EInfinity.Hammock.FreeHammockLocalizationWeak
public import SerrePositivity.EInfinity.Hammock.FixedObjectHomTransportIso

/-!
# 元の全自由次数の既存 DK Hom への右比較射の弱同値性

概要：同じ自由 hammock の各自由次数から既存 DK Hom への元の右射は弱同値。
方針：元の自由圏の局所化評価へ全自由次数を代入し、元の端点移送同型を合成する。
規約：元の freeHammockHomComparison 自身の成分を結論とする。
使われ方：DK 命題2.2の対角の右比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories

lemma freeHammockHomComparison_app_isWeakHomotopyEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (X Y : C.category) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeHammockHomComparison C X Y).app n) := by
  apply (freeHammockLocalizationObjects C).colimitValue_weak_of_localizationValue n X Y
  exact Hammock.free_localizationValue_isWeakHomotopyEquivalence
    (freeResolutionGeneratorBase C n).weakEquivalences
    (freeResolutionObject C n X) (freeResolutionObject C n Y)

end SerrePositivity.EInfinity.SimplicialLocalization
