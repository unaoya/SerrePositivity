module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutMiddleRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingFiveBlocks
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitFunctor

/-!
# 元の内部切断の refinedDiagram 全体の厳密な回収

概要：元の前後の語と括弧を保つ refinedDiagram を、元の同じ全図式へ圧縮する。
方針：内部三列の圧縮と middle の回収を、元の全語の貼り戻しへ接続する。
規約：元の全対象・全列・全縦射を保持する。端の空語も含む。
使われ方：hammock の指定 prefix と残りへの分解と元の標準射の照合。

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
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

def refinementMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i)) ⟶ w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingFiveBlocks.fiveBlocksMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.collapse ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i))
      (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.middle_word W τ i h).symm)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i)) ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w i)

lemma refinedDiagram_recovery :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (refinementMap W τ i h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram W τ i h) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ := by
  dsimp only [refinementMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingFiveBlocks.wordAction_fiveBlocks, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapse_blocks,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapsedColumn_eq_middle]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality.wordAction_append, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_id, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_eqToHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_roundtrip]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.recombine_eq i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

lemma refinedFunctor_recovery :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ i h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (refinementMap W τ i h) = τ := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_fixedFunctor (refinementMap W τ i h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram W τ i h)).symm.trans
    ((congrArg (fun F => F.fixedFunctor) (refinedDiagram_recovery W τ i h)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor_fixedFunctor τ))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
