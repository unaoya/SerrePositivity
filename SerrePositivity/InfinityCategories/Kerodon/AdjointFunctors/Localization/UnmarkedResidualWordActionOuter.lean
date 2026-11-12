module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedFactorSegments
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedFactorDirections
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorWordActionVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorBlockCuts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowReflection

/-!
# 元の残りの内部列以外の全横列と制限射

概要：後の語にある全列は、制限した元の語の作用と一致する。
方針：元の cut・後の連続部分の区間合成・方向付き列の回収を合成する。
規約：任意の列方向、全行、空 fiber を保持する。
使われ方：内部接続列と合わせた 残りの全図式の比較。

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
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (i : Fin a.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (hi : a.direction i = .forward)
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0) (f.orderHom i) ≠ [])
  (d : Fin (n.unop.len + 1)) (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length)

lemma residual_outer_direction :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).direction k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d))
      (k.natAdd 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).direction k)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom i) hT).obj d)
      (k.natAdd 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k)) := by
  let fp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi
  let δ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).direction k
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k.castSucc
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k.succ
  have hδ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom i)).direction (k.natAdd 1) = δ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k
  have huv : u ≤ v := by
    have hm := fp.cut_monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono _ _ (Fin.castSucc_le_succ k))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq] at hm
    change u.val ≤ v.val
    change 1 + u.val ≤ 1 + v.val at hm
    omega
  have hd : ∀ l : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after a i).length,
      u.val ≤ l.val → l.val < v.val → (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after a i).direction l = δ := by
    intro l hl hl'
    have hp : (fp.cut (k.natAdd 1).castSucc).val ≤ (l.natAdd 1).val := by
      change (fp.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex _ _ k.castSucc)).val ≤ 1 + l.val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq]
      exact Nat.add_le_add_left hl 1
    have hq : (l.natAdd 1).val < (fp.cut (k.natAdd 1).succ).val := by
      change 1 + l.val < (fp.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex _ _ k.succ)).val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq]
      exact Nat.add_lt_add_left hl' 1
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ l).symm.trans
      ((fp.fiber_direction (k.natAdd 1) (l.natAdd 1) hp hq).trans hδ)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq fp ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d) δ (k.natAdd 1) hδ
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq f i hi k.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq f i hi k.succ)
    (fp.cut_monotone (Fin.castSucc_le_succ (k.natAdd 1))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono _ _ huv)
    (fun l hl hl' => (fp.fiber_direction (k.natAdd 1) l hl hl').trans hδ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_right_direction _ _ δ u v hd)
  have hs := (hc.trans he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_segment_after W τ i h d δ u v huv hd)
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock b (f.orderHom i)
  have ho := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq δ (τ.obj d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_block f i k.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_block f i k.succ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock a i).vertex_monotone huv)
    (f.cut_monotone (Fin.castSucc_le_succ (B.column k)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock a i).interval_direction δ u v hd)
    (fun l hl hl' => (f.fiber_direction (B.column k) l hl hl').trans (B.direction_eq k))
  exact ((hs.trans ho).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f (τ.obj d) δ (B.column k) (B.direction_eq k)).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_direction_after W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom i) hT d δ k rfl).symm

lemma residual_outer_arrow :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d)).arrow (k.natAdd 1))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom i) hT).obj d).arrow
        (k.natAdd 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ k) ?_ ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_outer_direction W f τ i h hi hT d k)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_right]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_action_vertex W f τ i h hi hT d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).source k)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_right]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_action_vertex W f τ i h hi hT d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).target k)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
