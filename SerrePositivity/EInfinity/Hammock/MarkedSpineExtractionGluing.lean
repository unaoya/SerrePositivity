module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineGluing
public import SerrePositivity.EInfinity.Hammock.UnmarkedCutPasteRecovery

/-!
# 元の反復抽出の後の貼り戻しは元の恒等射

概要：元の任意の hammock の点を反復抽出して貼り戻すと同じ元の点へ戻る。
方針：空文字列の持ち上げの回収と一段の貼り戻しの回収を長さの減少で反復する。
規約：元の点を保持する片側の逆関係。逆向きの一意性は後続。
使われ方：元の hammock と実際の指定因子を持つ有限切断列との同型。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma glue_markedSpine (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    MarkedSpine.glue (markedSpine W Y n X x) = x := by
  classical
  by_cases hx : (colimitValue W X Y).app n x = []
  · rw [markedSpine_empty W Y n X x hx]
    exact congrArg (fun k => k.app n ⟨x, hx⟩) (AllMarked.emptyLift_inclusion W X Y)
  · rw [markedSpine_nonempty W Y n X ⟨x, hx⟩]
    change FactorTarget.pastePoint W X Y ((nonemptyCut W X Y).app n ⟨x, hx⟩).1
      ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.1
      (MarkedSpine.glue (markedSpine W Y n ((nonemptyCut W X Y).app n ⟨x, hx⟩).1.val.right
        ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.2)) = x
    exact (congrArg (FactorTarget.pastePoint W X Y ((nonemptyCut W X Y).app n ⟨x, hx⟩).1
      ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.1)
      (glue_markedSpine ((nonemptyCut W X Y).app n ⟨x, hx⟩).1.val.right
        ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.2)).trans
      (congrArg (fun k => k.app n ⟨x, hx⟩) (nonemptyCut_paste W X Y))
termination_by ((colimitValue W X Y).app n x).length
decreasing_by exact nonemptyCut_residual_length_lt W ⟨x, hx⟩

lemma extraction_gluing (X : Paths C) :
    extraction W Y X ≫ MarkedSpine.gluing W Y X = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y) := by
  ext n x
  exact glue_markedSpine W Y X x

lemma extraction_injective (X : Paths C) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((extraction W Y X).app n) := by
  intro x y h
  have hx := glue_markedSpine W Y X x
  have hy := glue_markedSpine W Y X y
  exact hx.symm.trans ((congrArg MarkedSpine.glue h).trans hy)

lemma gluing_surjective (X : Paths C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((MarkedSpine.gluing W Y X).app n) :=
  fun x => ⟨markedSpine W Y n X x, glue_markedSpine W Y X x⟩

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
