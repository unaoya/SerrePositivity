module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutMiddleRecovery
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingFiveBlocks
public import SerrePositivity.EInfinity.Hammock.ZigzagColumnSplitFunctor

/-!
# 元の内部切断の refinedDiagram 全体の厳密な回収

概要：元の前後の語と括弧を保つ refinedDiagram を、元の同じ全図式へ圧縮する。
方針：内部三列の圧縮と middle の回収を、元の全語の貼り戻しへ接続する。
規約：元の全対象・全列・全縦射を保持する。端の空語も含む。
使われ方：hammock の指定 prefix と残りへの分解と元の標準射の照合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

def refinementMap :
    Word.append
      (Word.append (Word.append (Word.ColumnSplit.before w i) (Word.single .forward))
        (Word.single .forward))
      (Word.append (Word.single .forward) (Word.ColumnSplit.after w i)) ⟶ w :=
  Word.fiveBlocksMap Word.ForwardTriple.collapse ≫
    Word.appendMap (Word.appendMap (𝟙 (Word.ColumnSplit.before w i))
      (eqToHom (middle_word W τ i h).symm)) (𝟙 (Word.ColumnSplit.after w i)) ≫
        eqToHom (Word.ColumnSplit.whole_eq w i)

lemma refinedDiagram_recovery :
    wordAction (refinementMap W τ i h) (refinedDiagram W τ i h) = ofFunctor τ := by
  dsimp only [refinementMap, refinedDiagram, prefixDiagram, residualDiagram]
  rw [wordAction_comp, wordAction_comp, wordAction_fiveBlocks, collapse_blocks,
    collapsedColumn_eq_middle]
  simp only [wordAction_append, wordAction_id, wordAction_eqToHom, changeWord_roundtrip]
  exact ColumnSplit.recombine_eq i (ofFunctor τ)

lemma refinedFunctor_recovery :
    refinedFunctor W τ i h ⋙ WordAction.functor (refinementMap W τ i h) = τ := by
  exact (wordAction_fixedFunctor (refinementMap W τ i h) (refinedDiagram W τ i h)).symm.trans
    ((congrArg (fun F => F.fixedFunctor) (refinedDiagram_recovery W τ i h)).trans
      (ofFunctor_fixedFunctor τ))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
