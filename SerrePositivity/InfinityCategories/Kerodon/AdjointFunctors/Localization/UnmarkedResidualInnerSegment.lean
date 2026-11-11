module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedInnerArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedFactorSegments
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentColumnFactorization

/-!
# 元の残りの内部接続列からの区間合成

概要：内部切断端点から残りの後の頂点までの合成を元の残りの射列へ照合する。
方針：接合点で分割し、元の内部列と後置区間を回収して合成する。
規約：元の各行・端点移送・同じ残りの射列を保持する。
使われ方：圧縮後の残り最初列の比較。

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
  (u : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length + 1))
  (hd : ∀ k : Fin w.length, i.castSucc.val ≤ k.val →
    k.val < ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u).val → w.direction k = .forward)

include hd in
lemma residual_inner_direction (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w i).length) (_hk : 0 ≤ k.val)
    (hk' : k.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i) u).val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w i).direction k = .forward := by
  cases k using Fin.addCases with
  | left k => rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]; rfl
  | right k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).direction_eq k).symm.trans
      (hd _ (by change i.val ≤ i.val + 1 + k.val; omega)
        (by
          change 1 + k.val < 1 + u.val at hk'
          change i.val + 1 + k.val < i.val + 1 + u.val
          omega))

lemma residual_inner_segment :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d) 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i) u) (Fin.zero_le _)
      (residual_inner_direction i u hd))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i h).app d).comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn (τ.obj d) i.castSucc ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u)
          hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega))) := by
  let P := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d
  let c : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w i).length := (0 : Fin 1).castAdd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length
  have hd' : ∀ k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length,
      (0 : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length + 1)).val ≤ k.val → k.val < u.val →
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).direction k = .forward := by
    intro k _ hk
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).direction_eq k).symm.trans
      (hd _ (by change i.val ≤ i.val + 1 + k.val; omega)
        (by change i.val + 1 + k.val < i.val + 1 + u.val; omega))
  have hpost := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_segment_after W τ i h d .forward 0 u (Fin.zero_le _) hd'
  have hstart : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex 0 = i.succ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex w i 0).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex_zero w i)
  have hq : i.val + 1 ≤ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u).val := by
    change i.val + 1 ≤ i.val + 1 + u.val
    omega
  have hpost' := hpost.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq .forward (τ.obj d) hstart rfl
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex_monotone (Fin.zero_le u)) hq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).interval_direction .forward 0 u hd')
    (fun k hk hk' => hd k (by change i.val + 1 ≤ k.val at hk; change i.val ≤ k.val; omega) hk'))
  have ht : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward P c.succ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i) u)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i) (Fin.zero_le u))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_right_direction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i)
        .forward 0 u hd'))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn (τ.obj d) i.castSucc ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u)
        hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega)) := by
    have hn : HEq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn (τ.obj d) i.castSucc ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u)
          hd i (by rfl) (by change i.val < i.val + 1 + u.val; omega))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward (τ.obj d) i.succ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w i).vertex u) hq
          (fun k hk hk' => hd k
            (by change i.val + 1 ≤ k.val at hk; change i.val ≤ k.val; omega) hk')) := by
      exact eqToHom_comp_heq _ _
    exact hpost'.trans hn.symm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward P 0 c.succ _ (Fin.zero_le _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i) (Fin.zero_le u))]
  have hl := (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward P c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i)
      (0 : Fin 1)))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_inner_arrow W τ i h d)
  exact heq_comp P.first
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W τ i h).obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).obj d) 0).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).obj d).first).trans
      (congrArg (fun F => F.obj d) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint_eq_rowTarget W τ i h)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertex W τ i h d u).trans
      (congrArg (τ.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex w i u)).symm)
    hl ht

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
