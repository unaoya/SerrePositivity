module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedInnerArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedFactorSegments
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentColumnFactorization

/-!
# 元の prefix の内部接続列までの区間合成

概要：prefix の前の頂点から内部切断端点までの合成を元の接頭射へ照合する。
方針：接合点で分割し、元の前置区間と内部列を回収して合成する。
規約：元の各行・端点移送・同じ接頭射列を保持する。
使われ方：圧縮後の prefix 最終列の比較。

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
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1))
  (u : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length + 1))
  (hd : ∀ k : Fin w.length, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u).val ≤ k.val →
    k.val < i.succ.val → w.direction k = .forward)

include hd in
lemma prefix_inner_direction (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).length)
    (hk : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) u).val ≤ k.val)
    (_hk' : k.val < (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).length).val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).direction k = .forward := by
  cases k using Fin.addCases with
  | left k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).direction_eq k).symm.trans
      (hd _ (by change 0 + u.val ≤ 0 + k.val; change u.val ≤ k.val at hk; omega)
        (by have hb := k.isLt; change k.val < i.val at hb; change 0 + k.val < i.val + 1; omega))
  | right k => rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]; rfl

lemma prefix_inner_segment :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).obj d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) u)
      (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).length) (Fin.le_last _)
      (prefix_inner_direction i u hd))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u) i.succ hd i
        (by have hu := u.isLt; change u.val < i.val + 1 at hu; change 0 + u.val ≤ i.val; omega)
        (by change i.val < i.val + 1; omega)).comp ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i h).app d)) := by
  let P := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).obj d
  let c : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).length := (0 : Fin 1).natAdd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length
  let v := Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length
  have hd' : ∀ k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length,
      u.val ≤ k.val → k.val < v.val → (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).direction k = .forward := by
    intro k hk _
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).direction_eq k).symm.trans
      (hd _ (by change 0 + u.val ≤ 0 + k.val; omega)
        (by have hb := k.isLt; change k.val < i.val at hb; change 0 + k.val < i.val + 1; omega))
  have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_segment_before W τ i h d .forward u v (Fin.le_last _) hd'
  have hend : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex v = i.castSucc :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex w i v).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex_last w i)
  have hp : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u).val ≤ i.val := by
    have hu := u.isLt
    change u.val < i.val + 1 at hu
    change 0 + u.val ≤ i.val
    omega
  have hpre' := hpre.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq .forward (τ.obj d) rfl hend
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex_monotone (Fin.le_last u)) hp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).interval_direction .forward u v hd')
    (fun k hk hk' => hd k hk (by change k.val < i.val at hk'; change k.val < i.val + 1; omega)))
  have ht : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward P
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) u) c.castSucc
      (by change u.val ≤ i.val; have hu := u.isLt; change u.val < i.val + 1 at hu; omega)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_left_direction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
        .forward u v hd'))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u) i.succ hd i
        hp (by change i.val < i.val + 1; omega)) := by
    have hn : HEq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u) i.succ hd i
          hp (by change i.val < i.val + 1; omega))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward (τ.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w i).vertex u) i.castSucc
          hp (fun k hk hk' => hd k hk
            (by change k.val < i.val at hk'; change k.val < i.val + 1; omega))) := by
      exact comp_eqToHom_heq _ _
    exact hpre'.trans hn.symm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward P _ c.castSucc _
    (by change u.val ≤ i.val; have hu := u.isLt; change u.val < i.val + 1 at hu; omega)
    (by change i.val ≤ i.val + 1; omega)]
  have hl := (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward P c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1)))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_inner_arrow W τ i h d)
  exact heq_comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertex W τ i h d u).trans
      (congrArg (τ.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex w i u)).symm)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ i h).obj d) v).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).obj d).last).trans
      (congrArg (fun F => F.obj d) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint_eq_rowSource W τ i h))) P.last
    ht hl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
