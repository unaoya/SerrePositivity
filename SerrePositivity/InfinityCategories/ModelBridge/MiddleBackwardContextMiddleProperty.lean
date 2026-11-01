module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardContextColumn

/-!
# 元の全体の中央列と抽出した中央の脚の性質

概要：元の全体の同じ中央列の性質を、抽出した局所図式の中央の脚へ戻す。
方針：元の恒等関手との厳密な回収と、連結の列の移送を使う。
規約：性質は任意の射の性質でよく、自明性を未知の入力にしない。
使われ方：元の全部分圏の条件から右置換の入力の自明性を回収する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

lemma middleColumn_property (P : MorphismProperty C)
    (S : Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) :
    P (S.arrow (middleColumn a b n m)) ↔ P ((coreFamily a b n m X Y).middle.app S) := by
  have h : P (((rebuiltFunctor a b n m X Y).obj S).arrow (middleColumn a b n m)) ↔
      P ((coreFamily a b n m X Y).middle.app S) := by
    change P ((ZigzagAppend.obj
      (ZigzagAppend.obj ((prefixDiagram a b n m X Y).obj S)
        ((coreFamily a b n m X Y).zigzagObj S))
      ((suffixDiagram a b n m X Y).obj S)).arrow (middleColumn a b n m)) ↔ _
    dsimp only [middleColumn]
    rw [ZigzagAppend.arrow_left_property P, ZigzagAppend.arrow_right_property P]
    exact (coreFamily a b n m X Y).middleColumn_property P S
  rw [rebuiltFunctor_eq] at h
  exact h

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
