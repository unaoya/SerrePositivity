module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockAppend

/-!
# 元の自由射列の交互単色ブロックへの正規化

概要：最後の文字を逐次追加し、元の自由射列を同じ生成矢の交互ブロックへ移す。
方針：同色の追加は最後のブロックへ結合し、異色なら新しいブロックを始める。
規約：flatten は元の射列そのものを回収する。
使われ方：自由積の交互標準形の存在と一意性。

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

def normalize {X : C} : ∀ {Y : C}, Quiver.Path X Y → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y
  | _, .nil => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty W X
  | _, .cons p f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetter W (normalize p) f

lemma normalize_cons {X Y Z : C} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    normalize W (p.cons f) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetter W (normalize W p) f := rfl

lemma flatten_normalize {X Y : C} (p : Quiver.Path X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W (normalize W p) = p := by
  induction p with
  | nil => rfl
  | cons p f ih => rw [normalize_cons, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_appendLetter, ih]

lemma appendBlock_positive {X Y Z : C} {previous : Option Bool} (initial : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y)
    (c : Bool) (block : Quiver.Path Y Z) (positive : 0 < block.length)
    (uniform : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.monochrome W c).paths block) (alternate : previous ≠ some c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock W initial c block uniform alternate =
      ⟨some c, .snoc initial c block positive uniform alternate⟩ := by
  cases block with
  | nil => simp at positive
  | cons q f => rfl

lemma appendLetter_appendBlock {X Y Z T : C} {previous : Option Bool}
    (initial : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y) (c : Bool) (block : Quiver.Path Y Z)
    (uniform : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.monochrome W c).paths block) (alternate : previous ≠ some c)
    (f : Z ⟶ T) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f = c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetter W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock W initial c block uniform alternate) f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock W initial c (block.cons f) ⟨uniform, hf⟩ alternate := by
  classical
  cases block with
  | nil =>
    cases initial with
    | nil => cases hf; rfl
    | snoc initial' c' block' positive' uniform' alternate' =>
      have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.color W f ≠ c' := by
        intro he
        exact alternate (congrArg some (he.symm.trans hf))
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetter, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetterForm]
      rw [dite_eq_right hn]
      cases hf
      rfl
  | cons q g =>
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetter, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendLetterForm]
    rw [dite_eq_left hf]

lemma normalize_appendBlock {X Y Z : C} {previous : Option Bool}
    (initial : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X previous Y) (c : Bool) (block : Quiver.Path Y Z)
    (uniform : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.monochrome W c).paths block) (alternate : previous ≠ some c)
    (hi : normalize W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten W initial) = ⟨previous, initial⟩) :
    normalize W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten W initial).comp block) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock W initial c block uniform alternate := by
  induction block with
  | nil => exact hi
  | cons q f ih =>
    rw [Quiver.Path.comp_cons, normalize_cons, ih uniform.1]
    exact appendLetter_appendBlock W initial c q uniform.1 alternate f uniform.2

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
