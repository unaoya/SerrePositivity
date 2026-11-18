module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardEquivalence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.NerveWeakTransport

/-!
# 元の前向き二列の切断関手の nerve の弱同値性

概要：元の固定語の切断関手自身が nerve の弱同値を誘導する。
方針：同じ切断関手を関手部分とする元の圏同値を使う。
規約：モデル構造や圏の groupoid 性を要求しない。
使われ方：DK9.4・10.3の元の graph の分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
lemma forwardForwardEquivalence_functor :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardEquivalence W w X Y).functor = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y := rfl
lemma forwardForwardFunctor_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.nerveMap_equivalence_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardEquivalence W w X Y)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
