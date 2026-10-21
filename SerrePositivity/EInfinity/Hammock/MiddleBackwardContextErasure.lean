module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardContextRightIdentity
public import SerrePositivity.EInfinity.Hammock.WordErasure
public import SerrePositivity.EInfinity.Hammock.WordEmbeddingFull

/-!
# 任意の前後の語の中の元の中央列の挿入

概要：元の eraseInclusion の WordAction を、中央自明 cofibration の全部分圏へ移す。
方針：挿入の像の中央列は恒等列なので自明 cofibration。全忠実性も回収する。
規約：元の削除語と元の挿入をそのまま使用する。
使われ方：全忠実な元の挿入を通した右置換の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

abbrev sourceWord := Word.erase (wholeWord a b n m) (middleColumn a b n m)

abbrev wordMap := Word.eraseInclusion (wholeWord a b n m) (middleColumn a b n m)

def originalFunctor : Zigzag (weakEquivalences C) (sourceWord a b n m) X Y ⥤
    Zigzag (weakEquivalences C) (wholeWord a b n m) X Y :=
  WordAction.functor (wordMap a b n m)

instance originalFunctor_full : (originalFunctor a b n m X Y).Full :=
  WordAction.functor_full _ (Word.eraseInclusion_injective _ _)

instance originalFunctor_faithful : (originalFunctor a b n m X Y).Faithful :=
  WordAction.functor_faithful _ (Word.eraseInclusion_injective _ _)

lemma originalFunctor_middle_trivial (S : Zigzag (weakEquivalences C) (sourceWord a b n m) X Y) :
    TrivialCofibration.property a b n m X Y ((originalFunctor a b n m X Y).obj S) := by
  have h := (identityOutside_erase_iff (WordAction.obj (wordMap a b n m) S)
    (middleColumn a b n m)).1 (WordAction.identityOutside_obj (wordMap a b n m) S)
  have : IsIso ((WordAction.obj (wordMap a b n m) S).arrow (middleColumn a b n m)) := by
    rw [h.arrow_eq]
    infer_instance
  change trivialCofibrations C ((WordAction.obj (wordMap a b n m) S).arrow (middleColumn a b n m))
  exact (trivialCofibrations C).of_isIso _

def functor : Zigzag (weakEquivalences C) (sourceWord a b n m) X Y ⥤
    TrivialCofibration.Objects a b n m X Y :=
  (TrivialCofibration.property a b n m X Y).lift (originalFunctor a b n m X Y)
    (originalFunctor_middle_trivial a b n m X Y)

lemma functor_comp_inclusion : functor a b n m X Y ⋙ TrivialCofibration.inclusion a b n m X Y =
    originalFunctor a b n m X Y := rfl

instance functor_full : (functor a b n m X Y).Full := by
  have : (functor a b n m X Y ⋙ TrivialCofibration.inclusion a b n m X Y).Full :=
    inferInstanceAs (originalFunctor a b n m X Y).Full
  exact Functor.Full.of_comp_faithful _ (TrivialCofibration.inclusion a b n m X Y)

instance functor_faithful : (functor a b n m X Y).Faithful := by
  have : (functor a b n m X Y ⋙ TrivialCofibration.inclusion a b n m X Y).Faithful :=
    inferInstanceAs (originalFunctor a b n m X Y).Faithful
  exact Functor.Faithful.of_comp _ (TrivialCofibration.inclusion a b n m X Y)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
