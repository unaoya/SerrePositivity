module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorPartition

/-!
# 元の自由射列の交互単色ブロック

概要：空でない単色の射列を交互に連ねた、元の自由射列の標準形の型。
方針：最終色を添字に持ち、隣接ブロックの異色性を構成子で保証する。
規約：色は元の生成矢の W 所属で決める。恒等文字を消さない。
使われ方：元の自由積の交互分解と hammock の行の分解。

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

def color {X Y : C} (f : X ⟶ Y) : Bool := by
  classical
  exact decide (W f)

def monochrome (c : Bool) : MorphismProperty C := fun _ _ f => color W f = c

lemma color_true_iff {X Y : C} (f : X ⟶ Y) : color W f = true ↔ W f := by
  classical
  simp [color]

lemma color_false_iff {X Y : C} (f : X ⟶ Y) : color W f = false ↔ ¬ W f := by
  classical
  simp [color]

inductive Form (X : C) : Option Bool → C → Type (max u v)
  | nil : Form X none X
  | snoc {Y Z : C} {previous : Option Bool} (initial : Form X previous Y)
      (c : Bool) (block : Quiver.Path Y Z) (positive : 0 < block.length)
      (uniform : (monochrome W c).paths block) (alternate : previous ≠ some c) :
      Form X (some c) Z

def Normal (X Y : C) := Σ c, Form W X c Y

def flatten {X : C} : ∀ {c : Option Bool} {Y : C}, Form W X c Y → Quiver.Path X Y
  | _, _, .nil => .nil
  | _, _, .snoc initial _ block _ _ _ => (flatten initial).comp block

def flattenNormal {X Y : C} (N : Normal W X Y) : Quiver.Path X Y := flatten W N.2

def empty (X : C) : Normal W X X := ⟨none, .nil⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
