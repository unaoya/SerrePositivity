module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineSimplex

/-!
# 元の hammock の反復切断の単体的自然性

概要：実際の指定因子を持つ有限切断列への構成を元の全単体作用素へ照合する。
方針：空文字列部分の元の同型の自然性と一段の切断の自然性を、長さの減少で反復する。
規約：元の全点・全指定因子・同じ生成矢を保持する。
使われ方：自由積分解の元の反復切断射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  {n m : SimplexCategoryᵒᵖ}

lemma markedSpine_simplex (θ : n ⟶ m) (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    MarkedSpine.map θ (markedSpine W Y n X x) =
      markedSpine W Y m X ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ x) := by
  classical
  by_cases hx : (colimitValue W X Y).app n x = []
  · have hθ := (EmptyValue.value_simplex W X Y θ x).trans hx
    rw [markedSpine_empty W Y n X x hx, markedSpine_empty W Y m X _ hθ]
    apply congrArg (MarkedSpine.nil X)
    exact (congrArg (fun k => k ⟨x, hx⟩) ((AllMarked.emptyLift W X Y).naturality θ)).symm
  · have hθ : (colimitValue W X Y).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ x) ≠ [] :=
      fun he => hx ((EmptyValue.value_simplex W X Y θ x).symm.trans he)
    rw [markedSpine_nonempty W Y n X ⟨x, hx⟩, markedSpine_nonempty W Y m X ⟨_, hθ⟩]
    have hc : (nonemptyCut W X Y).app m ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ x, hθ⟩ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).map θ ((nonemptyCut W X Y).app n ⟨x, hx⟩) :=
      congrArg (fun k => k ⟨x, hx⟩) ((nonemptyCut W X Y).naturality θ)
    rw [hc]
    exact congrArg (fun t => MarkedSpine.cons X ((nonemptyCut W X Y).app n ⟨x, hx⟩).1
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X ((nonemptyCut W X Y).app n ⟨x, hx⟩).1.val).map θ
        ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.1) t)
      (markedSpine_simplex θ ((nonemptyCut W X Y).app n ⟨x, hx⟩).1.val.right
        ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.2)
termination_by ((colimitValue W X Y).app n x).length
decreasing_by exact nonemptyCut_residual_length_lt W ⟨x, hx⟩

def extraction (X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ MarkedSpine.space W Y X where
  app n := ↾fun x => markedSpine W Y n X x
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (markedSpine_simplex W Y θ X x).symm

lemma extraction_wordValue (X : Paths C) :
    extraction W Y X ≫ MarkedSpine.wordValue W Y X = colimitValue W X Y := by
  ext n x
  exact markedSpine_word W Y n X x

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
