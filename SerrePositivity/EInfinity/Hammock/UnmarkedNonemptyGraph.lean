module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstColumnSimplex
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstColumnWordAction
public import SerrePositivity.EInfinity.Hammock.Diagram

/-!
# 非指定文字を含む元の hammock graph の単体的部分

概要：少なくとも一つの非空の非指定列を持つ元の単体を保つ単体集合を構成する。
方針：元の全単体作用素と非空性の保持を使う。
規約：元の全行・全列・全縦射を含む単体を使う。
使われ方：一段の切断射の始域と全語の余極限への降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.NonemptyGraph
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  (w : Word) (X Y : Paths C)

def simplicialSet : SSet.{max u v} where
  obj n := {τ : (graph W.paths w X Y).obj n // ∃ j, column W (τ.obj 0) j ≠ []}
  map θ := ↾fun τ => ⟨(graph W.paths w X Y).map θ τ.val,
    simplex_nonemptyColumns W τ.val τ.property θ⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact congrArg (fun f => f τ.val) ((graph W.paths w X Y).map_id n)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact congrArg (fun f => f τ.val) ((graph W.paths w X Y).map_comp θ φ)

def inclusion : simplicialSet W w X Y ⟶ graph W.paths w X Y where
  app _ := ↾fun τ => τ.val
  naturality _ _ _ := rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.NonemptyGraph
