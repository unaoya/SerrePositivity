module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardEquivalence
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

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
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
lemma forwardForwardEquivalence_functor :
    (forwardForwardEquivalence W w X Y).functor = forwardForwardFunctor W w X Y := rfl
lemma forwardForwardFunctor_weak :
    IsWeakHomotopyEquivalence (nerveMap (forwardForwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (forwardForwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
