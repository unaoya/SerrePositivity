module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitDirections
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendDirections

/-!
# 元の切断因子の外側の方向付き列

概要：prefix の前と残りの後の全列を元の方向付き列へ戻す。
方針：元の連結と切断図式の方向付き列の回収を合成する。
規約：元の全行と任意の列方向を含む。
使われ方：制限射で圧縮した因子の外側の横の列の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1)) (δ : Direction)

lemma prefix_direction_before (k : Fin (Word.ColumnSplit.before w i).length)
    (hk : (Word.ColumnSplit.before w i).direction k = δ) :
    HEq (Direction.arrow δ ((prefixDiagram W τ i h).obj d) (k.castAdd 1)
      ((Word.append_direction_left _ _ k).trans hk))
      (Direction.arrow δ (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).column k)
        (((Word.ColumnSplit.beforeBlock w i).direction_eq k).trans hk)) :=
  (ZigzagAppend.direction_left_heq ((beforeDiagram W τ i).obj d)
    ((leftBlock W τ i h).obj d) δ k hk).trans
    (ColumnSplit.before_direction_arrow i (ofFunctor τ) d δ k hk)

lemma residual_direction_after (k : Fin (Word.ColumnSplit.after w i).length)
    (hk : (Word.ColumnSplit.after w i).direction k = δ) :
    HEq (Direction.arrow δ ((residualDiagram W τ i h).obj d) (k.natAdd 1)
      ((Word.append_direction_right _ _ k).trans hk))
      (Direction.arrow δ (τ.obj d) ((Word.ColumnSplit.afterBlock w i).column k)
        (((Word.ColumnSplit.afterBlock w i).direction_eq k).trans hk)) :=
  (ZigzagAppend.direction_right_heq ((rightBlock W τ i h).obj d)
    ((afterDiagram W τ i).obj d) δ k hk).trans
    (ColumnSplit.after_direction_arrow i (ofFunctor τ) d δ k hk)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
