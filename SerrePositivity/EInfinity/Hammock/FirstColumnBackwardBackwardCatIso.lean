module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardBackwardEquivalence
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
  (w : Word) (X Y : C)
lemma backwardBackwardFunctor_obj_bijective :
    Function.Bijective (backwardBackwardFunctor W w X Y).obj := by
  constructor
  · intro S T h
    have he := congrArg (backwardBackwardRebuild W w X Y) h
    simpa only [backwardBackwardRebuild_functor_obj] using he
  · intro Z
    exact ⟨backwardBackwardRebuild W w X Y Z, backwardBackwardRebuild_object W w X Y Z⟩

instance backwardBackwardFunctor_isIso : (backwardBackwardFunctor W w X Y).IsIso where
  bijective_obj := backwardBackwardFunctor_obj_bijective W w X Y

def backwardBackwardCatIso : Cat.of (backwardBackwardSource W w X Y) ≅
    Cat.of (backwardBackwardTarget W w X Y) where
  hom := (backwardBackwardFunctor W w X Y).toCatHom
  inv := (backwardBackwardFunctor W w X Y).asIsomorphism.inverse.toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom
    (backwardBackwardFunctor W w X Y).asIsomorphism.unit_eq.symm
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom
    (backwardBackwardFunctor W w X Y).asIsomorphism.counit_eq

lemma backwardBackwardCatIso_hom : (backwardBackwardCatIso W w X Y).hom =
    (backwardBackwardFunctor W w X Y).toCatHom := rfl

def backwardBackwardGraphIso :
    graph W (Word.append (Word.single .backward) (Word.cons .backward w)) X Y ≅
      nerve (backwardBackwardTarget W w X Y) :=
  nerveFunctor.mapIso (backwardBackwardCatIso W w X Y)
lemma backwardBackwardGraphIso_hom : (backwardBackwardGraphIso W w X Y).hom =
    nerveMap (backwardBackwardFunctor W w X Y) := rfl
lemma backwardBackwardFunctor_weak :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (nerveMap (backwardBackwardFunctor W w X Y)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (backwardBackwardEquivalence W w X Y)
end SerrePositivity.EInfinity.Hammock.FirstColumn
