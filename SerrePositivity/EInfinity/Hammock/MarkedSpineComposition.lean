module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineGluingExtraction
public import SerrePositivity.EInfinity.Hammock.AllMarkedCompositionPoints

/-!
# 元の全因子列の明示的な合成

概要：接合点の指定二因子を元の指定 hammock 内で合成して全因子列を連結する。
方針：左の列で再帰し、終端で右の列の先頭の指定因子を合成する。
規約：元の全非指定生成矢と全指定因子を保持する。
使われ方：自由積の合成と元の hammock の合成との照合。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {X Y Z : Paths C} {n m : SimplexCategoryᵒᵖ}

def prepend (p : (AllMarked.nativeSpace W X Y).obj n) :
    MarkedSpine W Z n Y → MarkedSpine W Z n X
  | .nil _ q => .nil X (AllMarked.nativeComposePoint W X Y Z p q)
  | .cons _ g q t => .cons X g (AllMarked.nativeComposePoint W X Y g.val.left p q) t

def append {X : Paths C} : MarkedSpine W Y n X → MarkedSpine W Z n Y → MarkedSpine W Z n X
  | .nil _ p, t => prepend p t
  | .cons _ g p s, t => .cons X g p (append s t)

lemma prepend_simplex (θ : n ⟶ m) (p : (AllMarked.nativeSpace W X Y).obj n)
    (t : MarkedSpine W Z n Y) :
    prepend ((AllMarked.nativeSpace W X Y).map θ p) (map θ t) = map θ (prepend p t) := by
  cases t with
  | nil Y q =>
    exact congrArg (nil X) (AllMarked.nativeComposePoint_simplex W X Y Z θ p q)
  | cons Y g q t =>
    exact congrArg (fun r => cons X g r (map θ t))
      (AllMarked.nativeComposePoint_simplex W X Y g.val.left θ p q)

lemma append_simplex (θ : n ⟶ m) (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y) :
    append (map θ s) (map θ t) = map θ (append s t) := by
  induction s with
  | nil X p => exact prepend_simplex θ p t
  | cons X g p s ih =>
    exact congrArg (cons X g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p)) ih

lemma glue_prepend (p : (AllMarked.nativeSpace W X Y).obj n) (t : MarkedSpine W Z n Y) :
    glue (prepend p t) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X Y Z ((AllMarked.inclusion W X Y).app n p)
      (glue t) := by
  cases t with
  | nil Y q => exact AllMarked.inclusion_composePoint W X Y Z p q
  | cons Y g q t =>
    dsimp only [prepend, glue, FactorTarget.pastePoint]
    simp only [AllMarked.inclusion_composePoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_assoc]

lemma glue_append (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y) :
    glue (append s t) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X Y Z (glue s) (glue t) := by
  induction s with
  | nil X p => exact glue_prepend p t
  | cons X g p s ih =>
    change FactorTarget.pastePoint W X Z g p (glue (append s t)) = _
    rw [ih]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_assoc W.paths _ _ _).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
