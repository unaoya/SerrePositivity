module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutSpine
public import SerrePositivity.EInfinity.Hammock.AllMarkedEmptyIso

/-!
# 実際の指定 hammock を全因子に持つ有限切断列

概要：反復切断の終端も指定部分圏の実際の hammock に戻し、元の生成文字列を回収する。
方針：元の空文字列部分との同型の逆射を既存の有限切断列の終端に適用する。
規約：全 prefix・終端は実際の W-hammock、全生成矢は元の非指定 Total 矢である。
使われ方：自由積分解の単体的自然性と貼り戻しの逆構成。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  (n : SimplexCategoryᵒᵖ)

inductive MarkedSpine : Paths C → Type u
  | nil (X : Paths C) (p : (AllMarked.nativeSpace W X Y).obj n) : MarkedSpine X
  | cons (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
      (tail : MarkedSpine g.val.right) : MarkedSpine X

variable {W Y n}

def MarkedSpine.word {X : Paths C} : MarkedSpine W Y n X → List (Quiver.Total C)
  | .nil _ _ => []
  | .cons _ g _ t => g.val :: t.word

def Spine.marked {X : Paths C} : Spine W Y n X → MarkedSpine W Y n X
  | .nil X x hx => .nil X ((AllMarked.emptyLift W X Y).app n ⟨x, hx⟩)
  | .cons X g p t => .cons X g p t.marked

lemma Spine.marked_word {X : Paths C} (t : Spine W Y n X) : t.marked.word = t.word := by
  induction t with
  | nil => rfl
  | cons X g p t ih => exact congrArg (List.cons g.val) ih

variable (W Y n)

def markedSpine (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) : MarkedSpine W Y n X :=
  (spine W Y n X x).marked

lemma markedSpine_word (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    (markedSpine W Y n X x).word = (colimitValue W X Y).app n x :=
  (Spine.marked_word (spine W Y n X x)).trans (spine_word W Y n X x)

lemma markedSpine_empty (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (hx : (colimitValue W X Y).app n x = []) : markedSpine W Y n X x =
      MarkedSpine.nil X ((AllMarked.emptyLift W X Y).app n ⟨x, hx⟩) := by
  unfold markedSpine
  rw [spine_empty W Y n X x hx]
  rfl

lemma markedSpine_nonempty (X : Paths C) (x : (NonemptyValue.space W X Y).obj n) :
    markedSpine W Y n X x.val = MarkedSpine.cons X ((nonemptyCut W X Y).app n x).1
      ((nonemptyCut W X Y).app n x).2.1
      (markedSpine W Y n ((nonemptyCut W X Y).app n x).1.val.right
        ((nonemptyCut W X Y).app n x).2.2) := by
  unfold markedSpine
  rw [spine_nonempty W Y n X x]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
