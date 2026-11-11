module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockForm

/-!
# 交互単色ブロックへの元の生成矢の追加

概要：最後のブロックと同色なら結合し、異色なら新しいブロックを追加する。
方針：最終色の添字と元の射列の cons を使い、元の flatten を厳密に保持する。
規約：空射列だけを空標準形とし、恒等文字にも一文字の長さを残す。
使われ方：元の射列の正規化と一意性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def appendLetterForm {X : C} : ∀ {previous : Option Bool} {Y Z : C},
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y → (Y ⟶ Z) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Z
  | _, _, _, .nil, f =>
    ⟨some (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f), .snoc .nil (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f) f.toPath (by simp) ⟨trivial, rfl⟩ (by simp)⟩
  | _, _, _, .snoc initial c block positive uniform alternate, f => by
    classical
    exact if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f = c then
      ⟨some c, .snoc initial c (block.cons f) (by simp) ⟨uniform, h⟩ alternate⟩
    else
      ⟨some (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f), .snoc (.snoc initial c block positive uniform alternate)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f) f.toPath (by simp) ⟨trivial, rfl⟩
          (by intro he; exact h (Option.some.inj he).symm)⟩

def appendLetter {X Y Z : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) (f : Y ⟶ Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Z :=
  appendLetterForm W N.2 f

lemma flatten_appendLetter {X Y Z : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) (f : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W (appendLetter W N f) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N).cons f := by
  rcases N with ⟨c, N⟩
  cases N with
  | nil => rfl
  | snoc initial c block positive uniform alternate =>
    dsimp only [appendLetter, appendLetterForm]
    by_cases h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f = c
    · rw [dite_eq_left h]
      rfl
    · rw [dite_eq_right h]
      rfl

def appendBlock {X Y Z : C} {previous : Option Bool} (initial : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y)
    (c : Bool) (block : Quiver.Path Y Z) (uniform : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.monochrome W c).paths block)
    (alternate : previous ≠ some c) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Z :=
  match block with
  | .nil => ⟨previous, initial⟩
  | .cons q f => ⟨some c, .snoc initial c (q.cons f) (by simp) uniform alternate⟩

lemma flatten_appendBlock {X Y Z : C} {previous : Option Bool} (initial : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y)
    (c : Bool) (block : Quiver.Path Y Z) (uniform : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.monochrome W c).paths block)
    (alternate : previous ≠ some c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W (appendBlock W initial c block uniform alternate) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten W initial).comp block := by
  cases block <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
