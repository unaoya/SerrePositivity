module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComparisonWeak
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak

/-!
# 元の自由 hammock の対角から既存 DK Hom への右比較射の弱同値性

概要：DK 命題2.2の元の右比較射自身は弱ホモトピー同値となる。
方針：各自由次数の元の右比較にモデル不要の対角定理を適用する。
規約：元の対角と既存 DK Hom の同じ離散対角同型を保持する。
使われ方：元の hammock と既存 DK Hom の高次比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories Hammock.DoubleSimplicial

lemma freeHammockDiagonalComparison_isWeakHomotopyEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeHammockDiagonalComparison C X Y) := by
  have hd := diagonalFunctor_map_weak (freeHammockHomComparison C X Y)
    (freeHammockHomComparison_app_isWeakHomotopyEquivalence C X Y)
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (localizationHom C X Y))).isWeakHomotopyEquivalence
  exact hd.comp hi

end SerrePositivity.EInfinity.SimplicialLocalization
