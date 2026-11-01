module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedFactorRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitSegments
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendSegments

/-!
# 元の prefix の前と残りの後の区間合成

概要：切断因子の前後の語の区間合成を、元の同じ区間へ回収する。
方針：連結の区間合成と切断図式の元の区間合成の回収を合成する。
規約：接合点・空区間・全方向を保持する。
使われ方：制限した語の射による外側の横の列の比較。
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

lemma prefix_segment_before (u v : Fin ((Word.ColumnSplit.before w i).length + 1))
    (huv : u ≤ v) (hd : ∀ j : Fin (Word.ColumnSplit.before w i).length,
      u.val ≤ j.val → j.val < v.val → (Word.ColumnSplit.before w i).direction j = δ) :
    HEq (Segment.map δ ((prefixDiagram W τ i h).obj d)
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) u)
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) v)
      (Word.leftVertex_mono _ _ huv) (Word.append_left_direction _ _ δ u v hd))
      (Segment.map δ (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).vertex u)
        ((Word.ColumnSplit.beforeBlock w i).vertex v)
        ((Word.ColumnSplit.beforeBlock w i).vertex_monotone huv)
        ((Word.ColumnSplit.beforeBlock w i).interval_direction δ u v hd)) :=
  (ZigzagAppend.map_left_heq ((beforeDiagram W τ i).obj d) ((leftBlock W τ i h).obj d)
    δ u v huv hd).trans (ColumnSplit.before_segment i (ofFunctor τ) d δ u v huv hd)

lemma residual_segment_after (u v : Fin ((Word.ColumnSplit.after w i).length + 1))
    (huv : u ≤ v) (hd : ∀ j : Fin (Word.ColumnSplit.after w i).length,
      u.val ≤ j.val → j.val < v.val → (Word.ColumnSplit.after w i).direction j = δ) :
    HEq (Segment.map δ ((residualDiagram W τ i h).obj d)
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) u)
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) v)
      (Word.rightVertex_mono _ _ huv) (Word.append_right_direction _ _ δ u v hd))
      (Segment.map δ (τ.obj d) ((Word.ColumnSplit.afterBlock w i).vertex u)
        ((Word.ColumnSplit.afterBlock w i).vertex v)
        ((Word.ColumnSplit.afterBlock w i).vertex_monotone huv)
        ((Word.ColumnSplit.afterBlock w i).interval_direction δ u v hd)) :=
  (ZigzagAppend.map_right_heq ((rightBlock W τ i h).obj d) ((afterDiagram W τ i).obj d)
    δ u v huv hd).trans (ColumnSplit.after_segment i (ofFunctor τ) d δ u v huv hd)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
