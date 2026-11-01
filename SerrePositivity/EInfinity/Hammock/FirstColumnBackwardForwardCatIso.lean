module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardForwardEquivalence
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
  (w : Word) (X Y : C)
lemma backwardForwardFunctor_obj_bijective :
    Function.Bijective (backwardForwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (backwardForwardRebuild W w X Y) h
    simpa only [backwardForwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨backwardForwardRebuild W w X Y Z, backwardForwardRebuild_object W w X Y Z⟩

instance backwardForwardFunctor_isIso : (backwardForwardFunctor W w X Y).IsIso where
  bijective_obj := backwardForwardFunctor_obj_bijective W w X Y

def backwardForwardCatIso : Cat.of (backwardForwardSource W w X Y) ≅
    Cat.of (backwardForwardTarget W w X Y) where
  hom := (backwardForwardFunctor W w X Y).toCatHom
  inv := (backwardForwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (backwardForwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (backwardForwardFunctor W w X Y).asIsomorphism.counit_eq

lemma backwardForwardCatIso_hom : (backwardForwardCatIso W w X Y).hom =
    (backwardForwardFunctor W w X Y).toCatHom := rfl

def backwardForwardGraphIso :
    graph W (Word.append (Word.single .backward) (Word.cons .forward w)) X Y ≅
      nerve (backwardForwardTarget W w X Y) :=
  nerveFunctor.mapIso (backwardForwardCatIso W w X Y)
lemma backwardForwardGraphIso_hom : (backwardForwardGraphIso W w X Y).hom =
    nerveMap (backwardForwardFunctor W w X Y) := rfl
lemma backwardForwardFunctor_weak :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (nerveMap (backwardForwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (backwardForwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
