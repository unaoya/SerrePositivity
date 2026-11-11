module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumn
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowSimplexGenerator

/-!
# 最初の非指定列の位置と元の全単体作用素

概要：基準行が変わる全単体作用素でも、最初の非指定列は元の同じ番号を持つ。
方針：全行での元の列の文字列の一致と最小列の一意性を使う。
規約：退化と全ての面を含み、列の元の位置を保持する。
使われ方：指定 prefix と残りの単体的整合。

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
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)

include h in
lemma simplex_nonemptyColumns :
    ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) j ≠ [] := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.simplexColumn_ne_nil W τ j hj θ⟩

lemma firstColumn_simplex
    (hθ : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) j ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) hθ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_row W τ (θ.unop.toOrderHom 0) h hθ).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
