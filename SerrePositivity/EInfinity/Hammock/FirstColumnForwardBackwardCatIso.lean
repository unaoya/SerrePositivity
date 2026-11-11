module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardBackwardEquivalence
public import Mathlib.CategoryTheory.IsoCat
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の混合二方向の圏と graph の厳密な同型

概要：元の切断関手は対象上の全単射でもあり、元の圏と nerve の厳密な同型を与える。
方針：元の対象の両往復と充満忠実性から Mathlib の IsIso を使う。
規約：同型の順方向は元の切断関手そのものである。
使われ方：DK9.4・10.3の単体図式に自然な同型を渡す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
lemma forwardBackwardFunctor_obj_bijective :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild W w X Y) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild W w X Y Z, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_object W w X Y Z⟩

instance forwardBackwardFunctor_isIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).IsIso where
  bijective_obj := forwardBackwardFunctor_obj_bijective W w X Y

def forwardBackwardCatIso : Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y) ≅
    Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardTarget W w X Y) where
  hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).toCatHom
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).asIsomorphism.counit_eq

lemma forwardBackwardCatIso_hom : (forwardBackwardCatIso W w X Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).toCatHom := rfl

def forwardBackwardGraphIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y ≅
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardTarget W w X Y) :=
  nerveFunctor.mapIso (forwardBackwardCatIso W w X Y)
lemma forwardBackwardGraphIso_hom : (forwardBackwardGraphIso W w X Y).hom =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y) := rfl
lemma forwardBackwardFunctor_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
