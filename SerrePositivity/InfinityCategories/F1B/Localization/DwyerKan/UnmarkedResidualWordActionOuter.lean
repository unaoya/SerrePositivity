module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedFactorSegments
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedFactorDirections
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFactorWordActionVertices
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorBlockCuts
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DirectionArrowReflection

/-!
# 元の残りの内部列以外の全横列と制限射

概要：後の語にある全列は、制限した元の語の作用と一致する。
方針：元の cut・後の連続部分の区間合成・方向付き列の回収を合成する。
規約：任意の列方向、全行、空 fiber を保持する。
使われ方：内部接続列と合わせた 残りの全図式の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (i : Fin a.length)
  (h : column W (τ.obj 0) i ≠ []) (hi : a.direction i = .forward)
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0) (f.orderHom i) ≠ [])
  (d : Fin (n.unop.len + 1)) (k : Fin (Word.ColumnSplit.after b (f.orderHom i)).length)

lemma residual_outer_direction :
    HEq (Direction.arrow ((Word.ColumnSplit.after b (f.orderHom i)).direction k)
      (WordAction.obj (Word.CutFactor.residualMap f i hi) ((residualDiagram W τ i h).obj d))
      (k.natAdd 1) (Word.append_direction_right _ _ k))
    (Direction.arrow ((Word.ColumnSplit.after b (f.orderHom i)).direction k)
      ((residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).obj d)
      (k.natAdd 1) (Word.append_direction_right _ _ k)) := by
  let fp := Word.CutFactor.residualMap f i hi
  let δ := (Word.ColumnSplit.after b (f.orderHom i)).direction k
  let u := residualCutVertex f i k.castSucc
  let v := residualCutVertex f i k.succ
  have hδ : (residualWord b (f.orderHom i)).direction (k.natAdd 1) = δ :=
    Word.append_direction_right _ _ k
  have huv : u ≤ v := by
    have hm := fp.cut_monotone (Word.rightVertex_mono _ _ (Fin.castSucc_le_succ k))
    rw [residual_cut_eq, residual_cut_eq] at hm
    change u.val ≤ v.val
    change 1 + u.val ≤ 1 + v.val at hm
    omega
  have hd : ∀ l : Fin (Word.ColumnSplit.after a i).length,
      u.val ≤ l.val → l.val < v.val → (Word.ColumnSplit.after a i).direction l = δ := by
    intro l hl hl'
    have hp : (fp.cut (k.natAdd 1).castSucc).val ≤ (l.natAdd 1).val := by
      change (fp.cut (Word.rightVertex _ _ k.castSucc)).val ≤ 1 + l.val
      rw [residual_cut_eq]
      exact Nat.add_le_add_left hl 1
    have hq : (l.natAdd 1).val < (fp.cut (k.natAdd 1).succ).val := by
      change 1 + l.val < (fp.cut (Word.rightVertex _ _ k.succ)).val
      rw [residual_cut_eq]
      exact Nat.add_lt_add_left hl' 1
    exact (Word.append_direction_right _ _ l).symm.trans
      ((fp.fiber_direction (k.natAdd 1) (l.natAdd 1) hp hq).trans hδ)
  have hc := WordAction.arrow_obj_heq fp ((residualDiagram W τ i h).obj d) δ (k.natAdd 1) hδ
  have he := WordAction.segment_heq_of_eq δ ((residualDiagram W τ i h).obj d)
    (residual_cut_eq f i hi k.castSucc) (residual_cut_eq f i hi k.succ)
    (fp.cut_monotone (Fin.castSucc_le_succ (k.natAdd 1))) (Word.rightVertex_mono _ _ huv)
    (fun l hl hl' => (fp.fiber_direction (k.natAdd 1) l hl hl').trans hδ)
    (Word.append_right_direction _ _ δ u v hd)
  have hs := (hc.trans he).trans (residual_segment_after W τ i h d δ u v huv hd)
  let B := Word.ColumnSplit.afterBlock b (f.orderHom i)
  have ho := WordAction.segment_heq_of_eq δ (τ.obj d)
    (residualCutVertex_block f i k.castSucc) (residualCutVertex_block f i k.succ)
    ((Word.ColumnSplit.afterBlock a i).vertex_monotone huv)
    (f.cut_monotone (Fin.castSucc_le_succ (B.column k)))
    ((Word.ColumnSplit.afterBlock a i).interval_direction δ u v hd)
    (fun l hl hl' => (f.fiber_direction (B.column k) l hl hl').trans (B.direction_eq k))
  exact ((hs.trans ho).trans
    (WordAction.arrow_obj_heq f (τ.obj d) δ (B.column k) (B.direction_eq k)).symm).trans
      (residual_direction_after W (τ ⋙ WordAction.functor f) (f.orderHom i) hT d δ k rfl).symm

lemma residual_outer_arrow :
    HEq ((WordAction.obj (Word.CutFactor.residualMap f i hi)
      ((residualDiagram W τ i h).obj d)).arrow (k.natAdd 1))
      (((residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).obj d).arrow
        (k.natAdd 1)) := by
  apply Direction.raw_arrow_heq_of _ _ _ _ _ (Word.append_direction_right _ _ k)
    (Word.append_direction_right _ _ k) ?_ ?_ (residual_outer_direction W f τ i h hi hT d k)
  · rw [Word.source_right]
    exact residual_action_vertex W f τ i h hi hT d
      ((Word.ColumnSplit.after b (f.orderHom i)).source k)
  · rw [Word.target_right]
    exact residual_action_vertex W f τ i h hi hT d
      ((Word.ColumnSplit.after b (f.orderHom i)).target k)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
