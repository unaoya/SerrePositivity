module

public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedInnerArrows
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedFactorSegments
public import SerrePositivity.EInfinity.Hammock.ForwardSegmentColumnFactorization

/-!
# 元の prefix の内部接続列までの区間合成

概要：prefix の前の頂点から内部切断端点までの合成を元の接頭射へ照合する。
方針：接合点で分割し、元の前置区間と内部列を回収して合成する。
規約：元の各行・端点移送・同じ接頭射列を保持する。
使われ方：圧縮後の prefix 最終列の比較。
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
  (u : Fin ((Word.ColumnSplit.before w i).length + 1))
  (hd : ∀ k : Fin w.length, ((Word.ColumnSplit.beforeBlock w i).vertex u).val ≤ k.val →
    k.val < i.succ.val → w.direction k = .forward)

include hd in
lemma prefix_inner_direction (k : Fin (prefixWord w i).length)
    (hk : (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) u).val ≤ k.val)
    (_hk' : k.val < (Fin.last (prefixWord w i).length).val) :
    (prefixWord w i).direction k = .forward := by
  cases k using Fin.addCases with
  | left k =>
    rw [Word.append_direction_left]
    exact ((Word.ColumnSplit.beforeBlock w i).direction_eq k).symm.trans
      (hd _ (by change 0 + u.val ≤ 0 + k.val; change u.val ≤ k.val at hk; omega)
        (by have hb := k.isLt; change k.val < i.val at hb; change 0 + k.val < i.val + 1; omega))
  | right k => rw [Word.append_direction_right]; rfl

lemma prefix_inner_segment :
    HEq (Segment.map .forward ((prefixDiagram W τ i h).obj d)
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) u)
      (Fin.last (prefixWord w i).length) (Fin.le_last _)
      (prefix_inner_direction i u hd))
      ((Segment.toColumn (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).vertex u) i.succ hd i
        (by have hu := u.isLt; change u.val < i.val + 1 at hu; change 0 + u.val ≤ i.val; omega)
        (by change i.val < i.val + 1; omega)).comp ((rowPrefix W τ i h).app d)) := by
  let P := (prefixDiagram W τ i h).obj d
  let c : Fin (prefixWord w i).length := (0 : Fin 1).natAdd (Word.ColumnSplit.before w i).length
  let v := Fin.last (Word.ColumnSplit.before w i).length
  have hd' : ∀ k : Fin (Word.ColumnSplit.before w i).length,
      u.val ≤ k.val → k.val < v.val → (Word.ColumnSplit.before w i).direction k = .forward := by
    intro k hk _
    exact ((Word.ColumnSplit.beforeBlock w i).direction_eq k).symm.trans
      (hd _ (by change 0 + u.val ≤ 0 + k.val; omega)
        (by have hb := k.isLt; change k.val < i.val at hb; change 0 + k.val < i.val + 1; omega))
  have hpre := prefix_segment_before W τ i h d .forward u v (Fin.le_last _) hd'
  have hend : (Word.ColumnSplit.beforeBlock w i).vertex v = i.castSucc :=
    (Word.ColumnSplit.beforeBlock_vertex w i v).trans (Word.ColumnSplit.beforeVertex_last w i)
  have hp : ((Word.ColumnSplit.beforeBlock w i).vertex u).val ≤ i.val := by
    have hu := u.isLt
    change u.val < i.val + 1 at hu
    change 0 + u.val ≤ i.val
    omega
  have hpre' := hpre.trans (WordAction.segment_heq_of_eq .forward (τ.obj d) rfl hend
    ((Word.ColumnSplit.beforeBlock w i).vertex_monotone (Fin.le_last u)) hp
    ((Word.ColumnSplit.beforeBlock w i).interval_direction .forward u v hd')
    (fun k hk hk' => hd k hk (by change k.val < i.val at hk'; change k.val < i.val + 1; omega)))
  have ht : HEq (Segment.map .forward P
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) u) c.castSucc
      (by change u.val ≤ i.val; have hu := u.isLt; change u.val < i.val + 1 at hu; omega)
      (Word.append_left_direction (Word.ColumnSplit.before w i) (Word.single .forward)
        .forward u v hd'))
      (Segment.toColumn (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).vertex u) i.succ hd i
        hp (by change i.val < i.val + 1; omega)) := by
    have hn : HEq
        (Segment.toColumn (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).vertex u) i.succ hd i
          hp (by change i.val < i.val + 1; omega))
        (Segment.map .forward (τ.obj d) ((Word.ColumnSplit.beforeBlock w i).vertex u) i.castSucc
          hp (fun k hk hk' => hd k hk
            (by change k.val < i.val at hk'; change k.val < i.val + 1; omega))) := by
      exact comp_eqToHom_heq _ _
    exact hpre'.trans hn.symm
  rw [Segment.map_comp .forward P _ c.castSucc _
    (by change u.val ≤ i.val; have hu := u.isLt; change u.val < i.val + 1 at hu; omega)
    (by change i.val ≤ i.val + 1; omega)]
  have hl := (heq_of_eq (Segment.map_adjacent .forward P c
    (Word.append_direction_right (Word.ColumnSplit.before w i)
      (Word.single .forward) (0 : Fin 1)))).trans (prefix_inner_arrow W τ i h d)
  exact heq_comp
    ((prefix_vertex W τ i h d u).trans
      (congrArg (τ.obj d).vertex (Word.ColumnSplit.beforeBlock_vertex w i u)).symm)
    (((ZigzagAppend.vertex_left ((beforeDiagram W τ i).obj d) ((leftBlock W τ i h).obj d) v).trans
      ((beforeDiagram W τ i).obj d).last).trans
      (congrArg (fun F => F.obj d) (sourceJoint_eq_rowSource W τ i h))) P.last
    ht hl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
