module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDirections
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendDirections

/-!
# 元の切断因子の外側の方向付き列

概要：prefix の前と残りの後の全列を元の方向付き列へ戻す。
方針：元の連結と切断図式の方向付き列の回収を合成する。
規約：元の全行と任意の列方向を含む。
使われ方：制限射で圧縮した因子の外側の横の列の比較。

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
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1)) (δ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)

lemma prefix_direction_before (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length)
    (hk : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).direction k = δ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).obj d) (k.castAdd 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left _ _ k).trans hk))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).column k)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).direction_eq k).trans hk)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_left_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).obj d)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ i h).obj d) δ k hk).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_direction_arrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ) d δ k hk)

lemma residual_direction_after (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length)
    (hk : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).direction k = δ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d) (k.natAdd 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k).trans hk))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).column k)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).direction_eq k).trans hk)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_right_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W τ i h).obj d)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).obj d) δ k hk).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.after_direction_arrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ) d δ k hk)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
