module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardBackwardEquivalence
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
lemma forwardBackwardFunctor_obj_bijective :
    Function.Bijective (forwardBackwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (forwardBackwardRebuild W w X Y) h
    simpa only [forwardBackwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨forwardBackwardRebuild W w X Y Z, forwardBackwardRebuild_object W w X Y Z⟩

instance forwardBackwardFunctor_isIso : (forwardBackwardFunctor W w X Y).IsIso where
  bijective_obj := forwardBackwardFunctor_obj_bijective W w X Y

def forwardBackwardCatIso : Cat.of (forwardBackwardSource W w X Y) ≅
    Cat.of (forwardBackwardTarget W w X Y) where
  hom := (forwardBackwardFunctor W w X Y).toCatHom
  inv := (forwardBackwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (forwardBackwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (forwardBackwardFunctor W w X Y).asIsomorphism.counit_eq

lemma forwardBackwardCatIso_hom : (forwardBackwardCatIso W w X Y).hom =
    (forwardBackwardFunctor W w X Y).toCatHom := rfl

def forwardBackwardGraphIso :
    graph W (Word.append (Word.single .forward) (Word.cons .backward w)) X Y ≅
      nerve (forwardBackwardTarget W w X Y) :=
  nerveFunctor.mapIso (forwardBackwardCatIso W w X Y)
lemma forwardBackwardGraphIso_hom : (forwardBackwardGraphIso W w X Y).hom =
    nerveMap (forwardBackwardFunctor W w X Y) := rfl
lemma forwardBackwardFunctor_weak :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (nerveMap (forwardBackwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (forwardBackwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
