module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport

/-!
# 単体作用素による基準行の変更と同じ生成矢

概要：元の任意の単体作用素で全行を制限しても、最初の非指定生成矢は同じである。
方針：元の全行の非指定文字列の不変性と切断の Total 矢の一意性を使う。
規約：全単体作用素と元の nerve の写像を使う。
使われ方：切断図式の単体作用素への厳密な自然性。

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
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)

include h in
lemma simplexColumn_ne_nil : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [] := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj (θ.unop.toOrderHom 0)) i ≠ []
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_row W τ _ i]
  exact h

lemma rowGenerator_simplex
    (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_firstCut_row W τ (θ.unop.toOrderHom 0) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowFirstCut W τ i h 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowFirstCut W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ 0)).1.symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
