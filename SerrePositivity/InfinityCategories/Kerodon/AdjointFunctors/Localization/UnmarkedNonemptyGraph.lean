module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumnSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumnWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 非指定文字を含む元の hammock graph の単体的部分

概要：少なくとも一つの非空の非指定列を持つ元の単体を保つ単体集合を構成する。
方針：元の全単体作用素と非空性の保持を使う。
規約：元の全行・全列・全縦射を含む単体を使う。
使われ方：一段の切断射の始域と全語の余極限への降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : Paths C)

def simplicialSet : SSet.{max u v} where
  obj n := {τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n // ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []}
  map θ := ↾fun τ => ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ.val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.simplex_nonemptyColumns W τ.val τ.property θ⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact congrArg (fun f => f τ.val) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map_id n)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact congrArg (fun f => f τ.val) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map_comp θ φ)

def inclusion : simplicialSet W w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y where
  app _ := ↾fun τ => τ.val
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph
