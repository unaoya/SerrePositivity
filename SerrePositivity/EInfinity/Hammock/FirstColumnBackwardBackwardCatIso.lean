module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardEquivalence
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport
public import Mathlib.CategoryTheory.IsoCat

/-!
# 元の後向き二列の圏と graph の厳密な同型

概要：元の指定部分圏の Hom と残りの語の共変係数を保つ。
方針：同じ元の切断関手と全相対関手を使う。
規約：元の全対象・全縦射と端点表示を保持する。
使われ方：DK9.4・10.3の後向き二列の自然な分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
lemma backwardBackwardFunctor_obj_bijective :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild W w X Y) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild W w X Y Z, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild_object W w X Y Z⟩

instance backwardBackwardFunctor_isIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).IsIso where
  bijective_obj := backwardBackwardFunctor_obj_bijective W w X Y

def backwardBackwardCatIso : Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource W w X Y) ≅
    Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) where
  hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).toCatHom
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).asIsomorphism.counit_eq

lemma backwardBackwardCatIso_hom : (backwardBackwardCatIso W w X Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).toCatHom := rfl

def backwardBackwardGraphIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y ≅
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) :=
  nerveFunctor.mapIso (backwardBackwardCatIso W w X Y)
lemma backwardBackwardGraphIso_hom : (backwardBackwardGraphIso W w X Y).hom =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y) := rfl
lemma backwardBackwardFunctor_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
