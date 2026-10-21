module

public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedInnerArrows
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedFactorSegments
public import SerrePositivity.EInfinity.Hammock.ForwardSegmentColumnFactorization

/-!
# 元の残りの内部接続列からの区間合成

概要：内部切断端点から残りの後の頂点までの合成を元の残りの射列へ照合する。
方針：接合点で分割し、元の内部列と後置区間を回収して合成する。
規約：元の各行・端点移送・同じ残りの射列を保持する。
使われ方：圧縮後の残り最初列の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1))
  (u : Fin ((Word.ColumnSplit.after w i).length + 1))
  (hd : ∀ k : Fin w.length, i.castSucc.val ≤ k.val →
    k.val < ((Word.ColumnSplit.afterBlock w i).vertex u).val → w.direction k = .forward)

include hd in
lemma residual_inner_direction (k : Fin (residualWord w i).length) (_hk : 0 ≤ k.val)
    (hk' : k.val < (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) u).val) :
    (residualWord w i).direction k = .forward := by
  cases k using Fin.addCases with
  | left k => rw [Word.append_direction_left]; rfl
  | right k =>
    rw [Word.append_direction_right]
    exact ((Word.ColumnSplit.afterBlock w i).direction_eq k).symm.trans
      (hd _ (by change i.val ≤ i.val + 1 + k.val; omega)
        (by
          change 1 + k.val < 1 + u.val at hk'
          change i.val + 1 + k.val < i.val + 1 + u.val
          omega))

lemma residual_inner_segment :
    HEq (Segment.map .forward ((residualDiagram W τ i h).obj d) 0
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) u) (Fin.zero_le _)
      (residual_inner_direction i u hd))
      (((rowResidual W τ i h).app d).comp
        (Segment.fromColumn (τ.obj d) i.castSucc ((Word.ColumnSplit.afterBlock w i).vertex u)
          hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega))) := by
  let P := (residualDiagram W τ i h).obj d
  let c : Fin (residualWord w i).length := (0 : Fin 1).castAdd (Word.ColumnSplit.after w i).length
  have hd' : ∀ k : Fin (Word.ColumnSplit.after w i).length,
      (0 : Fin ((Word.ColumnSplit.after w i).length + 1)).val ≤ k.val → k.val < u.val →
        (Word.ColumnSplit.after w i).direction k = .forward := by
    intro k _ hk
    exact ((Word.ColumnSplit.afterBlock w i).direction_eq k).symm.trans
      (hd _ (by change i.val ≤ i.val + 1 + k.val; omega)
        (by change i.val + 1 + k.val < i.val + 1 + u.val; omega))
  have hpost := residual_segment_after W τ i h d .forward 0 u (Fin.zero_le _) hd'
  have hstart : (Word.ColumnSplit.afterBlock w i).vertex 0 = i.succ :=
    (Word.ColumnSplit.afterBlock_vertex w i 0).trans (Word.ColumnSplit.afterVertex_zero w i)
  have hq : i.val + 1 ≤ ((Word.ColumnSplit.afterBlock w i).vertex u).val := by
    change i.val + 1 ≤ i.val + 1 + u.val
    omega
  have hpost' := hpost.trans (WordAction.segment_heq_of_eq .forward (τ.obj d) hstart rfl
    ((Word.ColumnSplit.afterBlock w i).vertex_monotone (Fin.zero_le u)) hq
    ((Word.ColumnSplit.afterBlock w i).interval_direction .forward 0 u hd')
    (fun k hk hk' => hd k (by change i.val + 1 ≤ k.val at hk; change i.val ≤ k.val; omega) hk'))
  have ht : HEq (Segment.map .forward P c.succ
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) u)
      (Word.rightVertex_mono (Word.single .forward) (Word.ColumnSplit.after w i) (Fin.zero_le u))
      (Word.append_right_direction (Word.single .forward) (Word.ColumnSplit.after w i)
        .forward 0 u hd'))
      (Segment.fromColumn (τ.obj d) i.castSucc ((Word.ColumnSplit.afterBlock w i).vertex u)
        hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega)) := by
    have hn : HEq
        (Segment.fromColumn (τ.obj d) i.castSucc ((Word.ColumnSplit.afterBlock w i).vertex u)
          hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega))
        (Segment.map .forward (τ.obj d) i.succ ((Word.ColumnSplit.afterBlock w i).vertex u) hq
          (fun k hk hk' => hd k
            (by change i.val + 1 ≤ k.val at hk; change i.val ≤ k.val; omega) hk')) := by
      exact eqToHom_comp_heq _ _
    exact hpost'.trans hn.symm
  rw [Segment.map_comp .forward P 0 c.succ _ (Fin.zero_le _)
    (Word.rightVertex_mono (Word.single .forward) (Word.ColumnSplit.after w i) (Fin.zero_le u))]
  have hl := (heq_of_eq (Segment.map_adjacent .forward P c
    (Word.append_direction_left (Word.single .forward) (Word.ColumnSplit.after w i)
      (0 : Fin 1)))).trans (residual_inner_arrow W τ i h d)
  exact heq_comp P.first
    (((ZigzagAppend.vertex_right ((rightBlock W τ i h).obj d) ((afterDiagram W τ i).obj d) 0).trans
      ((afterDiagram W τ i).obj d).first).trans
      (congrArg (fun F => F.obj d) (targetJoint_eq_rowTarget W τ i h)))
    ((residual_vertex W τ i h d u).trans
      (congrArg (τ.obj d).vertex (Word.ColumnSplit.afterBlock_vertex w i u)).symm)
    hl ht

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
