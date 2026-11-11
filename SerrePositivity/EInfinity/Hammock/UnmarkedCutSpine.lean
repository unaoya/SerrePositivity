module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutRecursion

/-!
# 元の非空切断の有限回の反復と文字列の厳密な回収

概要：実際の指定 prefix と同じ生成矢を有限回取り出し、空文字列の残りまで到達する。
方針：既存の長さによる依存再帰を、元の文字列を回収する証明付きの切断列へ代入する。
規約：終端は元の空文字列の hammock の点。指定部分圏の hammock との同定は後続。
使われ方：自由積分解の反復部分と元の生成文字列への照合。
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

inductive Spine : Paths C → Type u
  | nil (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
      (empty : (colimitValue W X Y).app n x = []) : Spine X
  | cons (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
      (tail : Spine g.val.right) : Spine X

variable {W Y n}

def Spine.word {X : Paths C} : Spine W Y n X → List (Quiver.Total C)
  | .nil _ _ _ => []
  | .cons _ g _ t => g.val :: t.word

variable (W Y n)

def spineWithValue (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    {t : Spine W Y n X // t.word = (colimitValue W X Y).app n x} :=
  cutRec W Y n (fun X x => {t : Spine W Y n X // t.word = (colimitValue W X Y).app n x})
    (fun X x hx => ⟨Spine.nil X x hx, hx.symm⟩)
    (fun X x t => ⟨Spine.cons X ((nonemptyCut W X Y).app n x).1
      ((nonemptyCut W X Y).app n x).2.1 t.val,
      (congrArg (List.cons ((nonemptyCut W X Y).app n x).1.val) t.property).trans
        (nonemptyCut_value W x).symm⟩) X x

def spine (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) : Spine W Y n X :=
  (spineWithValue W Y n X x).val

lemma spine_word (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    (spine W Y n X x).word = (colimitValue W X Y).app n x :=
  (spineWithValue W Y n X x).property

lemma spine_empty (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (hx : (colimitValue W X Y).app n x = []) : spine W Y n X x = Spine.nil X x hx := by
  unfold spine spineWithValue
  rw [cutRec_empty W Y n _ _ _ X x hx]

lemma spine_nonempty (X : Paths C) (x : (NonemptyValue.space W X Y).obj n) :
    spine W Y n X x.val = Spine.cons X ((nonemptyCut W X Y).app n x).1
      ((nonemptyCut W X Y).app n x).2.1
      (spine W Y n ((nonemptyCut W X Y).app n x).1.val.right
        ((nonemptyCut W X Y).app n x).2.2) := by
  unfold spine spineWithValue
  rw [cutRec_nonempty W Y n _ _ _ X x]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
