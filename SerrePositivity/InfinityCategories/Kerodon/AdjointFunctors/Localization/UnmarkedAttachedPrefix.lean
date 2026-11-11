module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumnPrefix
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendArrowProperty

/-!
# 最初の非指定生成矢の始域までの指定 prefix

概要：元の前の全語と列内部の指定接頭射を接続し、全列・全縦射が指定であることを証明する。
方針：最初の列の最小性と元の連結の列の性質の回収を使う。
規約：固定端点の実際の関手を構成し、空の前の語も含む。
使われ方：指定部分圏の W-hammock への回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h0 : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [])

abbrev index := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h0

lemma nonempty : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0) ≠ [] := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h0

def diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h0)

def functor := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h0).fixedFunctor

lemma arrow_mem (k : Fin (n.unop.len + 1))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).length) : W.paths (((diagram W τ h0).obj k).arrow j) := by
  change W.paths ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ (index W τ h0)).obj k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ (index W τ h0) (nonempty W τ h0)).obj k)).arrow j)
  cases j using Fin.addCases with
  | left j =>
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property W.paths _ _ j).2
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFirstColumn_arrow_mem W τ h0 k j
  | right j =>
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property W.paths _ _ j).2
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock_arrow_mem W τ (index W τ h0) (nonempty W τ h0) k j

lemma map_mem {k l : Fin (n.unop.len + 1)} (f : k ⟶ l)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).length + 1)) : W.paths (((diagram W τ h0).map f).app j) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h0).map f).app_mem j

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix
