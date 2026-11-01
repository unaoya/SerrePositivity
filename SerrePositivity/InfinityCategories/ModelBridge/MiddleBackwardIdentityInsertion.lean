module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardTrivialRightReplacement
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.InsertBetweenActionObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingFull

/-!
# 元の中央恒等列の挿入と全部分圏への持ち上げ

概要：中央を飛ばす元の語の単射による WordAction を、自明中央列の全部分圏へ移す。
方針：空 fiber の中央列は元の等式の移送射であり、元の挿入は全忠実である。
規約：既存の語の作用そのものを使う。別の写像で代用しない。
使われ方：右置換の unit による第二の nerve 比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

abbrev sourceWord (n m : ℕ) : Word := Word.append (leftBoundaryWord n) (rightBoundaryWord m)
abbrev wordMap (n m : ℕ) : sourceWord n m ⟶ word n m :=
  Word.insertBetween (leftBoundaryWord n) (rightBoundaryWord m) .backward

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def originalFunctor : Zigzag (weakEquivalences C) (sourceWord n m) X Y ⥤
    Zigzag (weakEquivalences C) (word n m) X Y := WordAction.functor (wordMap n m)

instance originalFunctor_full :
    (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Full :=
  WordAction.functor_full _ (Word.insertBetween_injective _ _ _)

instance originalFunctor_faithful :
    (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Faithful :=
  WordAction.functor_faithful _ (Word.insertBetween_injective _ _ _)

lemma originalFunctor_middle_trivial (S : Zigzag (weakEquivalences C) (sourceWord n m) X Y) :
    TrivialCofibration.property (originalFunctor.obj S) := by
  have h := Word.insertBetween_cut_inserted (leftBoundaryWord n) (rightBoundaryWord m) .backward
  have he := (wordMap n m).cut_source_target_of_eq (Positions.middleColumn n m) h
  change trivialCofibrations C (WordAction.column (wordMap n m) S (Positions.middleColumn n m))
  have hc := WordAction.column_eqToHom_of_cut_eq (wordMap n m) S
    (Positions.middleColumn n m) h he
  have : IsIso (WordAction.column (wordMap n m) S (Positions.middleColumn n m)) := by
    rw [hc]
    infer_instance
  exact (trivialCofibrations C).of_isIso _

def functor : Zigzag (weakEquivalences C) (sourceWord n m) X Y ⥤
    TrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) :=
  TrivialCofibration.property.lift originalFunctor originalFunctor_middle_trivial

lemma functor_comp_inclusion : functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
    TrivialCofibration.inclusion = originalFunctor := rfl

instance functor_full : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Full := by
  have : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
      TrivialCofibration.inclusion).Full := inferInstanceAs originalFunctor.Full
  exact Functor.Full.of_comp_faithful _ TrivialCofibration.inclusion

instance functor_faithful :
    (functor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Faithful := by
  have : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
      TrivialCofibration.inclusion).Faithful := inferInstanceAs originalFunctor.Faithful
  exact Functor.Faithful.of_comp _ TrivialCofibration.inclusion

end SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
