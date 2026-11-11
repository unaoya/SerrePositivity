module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineLocalizationEvaluation

/-!
# 元の自由圏の局所化評価自身の弱同値性

概要：元の W.paths の全 hammock から同じ通常の局所化 Hom への評価は弱同値。
方針：元の全因子列への弱評価と同じ局所化 Hom 同型を実際の評価の等式で結ぶ。
規約：元の評価自身を結論とし、弱比較や可縮性を追加入力にしない。
使われ方：DK 比較補題2.3の全自由次数への適用。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories
open UnmarkedGenerators.FirstFactor.MarkedSpine

lemma free_localizationValue_isWeakHomotopyEquivalence {C : Type u} [Category.{u} C]
    (W : MorphismProperty C) (X Y : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (localizationValue W.paths X Y) := by
  rw [← hammockEvaluation_localizationValue W Y X]
  exact (hammockEvaluation_isWeakHomotopyEquivalence W Y X).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (valueLocalizationHomIso W X Y)).isWeakHomotopyEquivalence

end SerrePositivity.EInfinity.Hammock
