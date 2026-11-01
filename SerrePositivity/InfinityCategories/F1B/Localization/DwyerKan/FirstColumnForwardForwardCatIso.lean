module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardEquivalence
public import Mathlib.CategoryTheory.IsoCat

/-!
# 元の前向き二列の圏と graph の厳密な同型

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
lemma forwardForwardFunctor_obj_bijective :
    Function.Bijective (forwardForwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (forwardForwardRebuild W w X Y) h
    simpa only [forwardForwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨forwardForwardRebuild W w X Y Z, forwardForwardRebuild_object W w X Y Z⟩

instance forwardForwardFunctor_isIso : (forwardForwardFunctor W w X Y).IsIso where
  bijective_obj := forwardForwardFunctor_obj_bijective W w X Y

def forwardForwardCatIso : Cat.of (forwardForwardSource W w X Y) ≅
    Cat.of (forwardForwardTarget W w X Y) where
  hom := (forwardForwardFunctor W w X Y).toCatHom
  inv := (forwardForwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (forwardForwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (forwardForwardFunctor W w X Y).asIsomorphism.counit_eq

lemma forwardForwardCatIso_hom : (forwardForwardCatIso W w X Y).hom =
    (forwardForwardFunctor W w X Y).toCatHom := rfl

def forwardForwardGraphIso :
    graph W (Word.append (Word.single .forward) (Word.cons .forward w)) X Y ≅
      nerve (forwardForwardTarget W w X Y) :=
  nerveFunctor.mapIso (forwardForwardCatIso W w X Y)
lemma forwardForwardGraphIso_hom : (forwardForwardGraphIso W w X Y).hom =
    nerveMap (forwardForwardFunctor W w X Y) := rfl
end SerrePositivity.EInfinity.Hammock.FirstColumn
