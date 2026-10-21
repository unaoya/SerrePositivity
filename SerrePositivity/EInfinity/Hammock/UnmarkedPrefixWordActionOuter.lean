module

public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedFactorSegments
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedFactorDirections
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorWordActionVertices
public import SerrePositivity.EInfinity.Hammock.WordCutFactorBlockCuts
public import SerrePositivity.EInfinity.Hammock.DirectionArrowReflection

/-!
# 元の prefix の内部列以外の全横列と制限射

概要：前の語にある全列は、制限した元の語の作用と一致する。
方針：元の cut・前の連続部分の区間合成・方向付き列の回収を合成する。
規約：任意の列方向、全行、空 fiber を保持する。
使われ方：内部接続列と合わせた prefix 全図式の比較。
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
  (d : Fin (n.unop.len + 1)) (k : Fin (Word.ColumnSplit.before b (f.orderHom i)).length)

lemma prefix_outer_direction :
    HEq (Direction.arrow ((Word.ColumnSplit.before b (f.orderHom i)).direction k)
      (WordAction.obj (Word.CutFactor.prefixMap f i hi) ((prefixDiagram W τ i h).obj d))
      (k.castAdd 1) (Word.append_direction_left _ _ k))
    (Direction.arrow ((Word.ColumnSplit.before b (f.orderHom i)).direction k)
      ((prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).obj d)
      (k.castAdd 1) (Word.append_direction_left _ _ k)) := by
  let fp := Word.CutFactor.prefixMap f i hi
  let δ := (Word.ColumnSplit.before b (f.orderHom i)).direction k
  let u := prefixCutVertex f i k.castSucc
  let v := prefixCutVertex f i k.succ
  have hδ : (prefixWord b (f.orderHom i)).direction (k.castAdd 1) = δ :=
    Word.append_direction_left _ _ k
  have huv : u ≤ v := by
    have hm := fp.cut_monotone (Word.leftVertex_mono _ _ (Fin.castSucc_le_succ k))
    rw [prefix_cut_eq, prefix_cut_eq] at hm
    exact hm
  have hd : ∀ l : Fin (Word.ColumnSplit.before a i).length,
      u.val ≤ l.val → l.val < v.val → (Word.ColumnSplit.before a i).direction l = δ := by
    intro l hl hl'
    have hp : (fp.cut (k.castAdd 1).castSucc).val ≤ (l.castAdd 1).val := by
      change (fp.cut (Word.leftVertex _ _ k.castSucc)).val ≤ l.val
      rw [prefix_cut_eq]
      exact hl
    have hq : (l.castAdd 1).val < (fp.cut (k.castAdd 1).succ).val := by
      change l.val < (fp.cut (Word.leftVertex _ _ k.succ)).val
      rw [prefix_cut_eq]
      exact hl'
    exact (Word.append_direction_left _ _ l).symm.trans
      ((fp.fiber_direction (k.castAdd 1) (l.castAdd 1) hp hq).trans hδ)
  have hc := WordAction.arrow_obj_heq fp ((prefixDiagram W τ i h).obj d) δ (k.castAdd 1) hδ
  have he := WordAction.segment_heq_of_eq δ ((prefixDiagram W τ i h).obj d)
    (prefix_cut_eq f i hi k.castSucc) (prefix_cut_eq f i hi k.succ)
    (fp.cut_monotone (Fin.castSucc_le_succ (k.castAdd 1))) (Word.leftVertex_mono _ _ huv)
    (fun l hl hl' => (fp.fiber_direction (k.castAdd 1) l hl hl').trans hδ)
    (Word.append_left_direction _ _ δ u v hd)
  have hs := (hc.trans he).trans (prefix_segment_before W τ i h d δ u v huv hd)
  let B := Word.ColumnSplit.beforeBlock b (f.orderHom i)
  have ho := WordAction.segment_heq_of_eq δ (τ.obj d)
    (prefixCutVertex_block f i k.castSucc) (prefixCutVertex_block f i k.succ)
    ((Word.ColumnSplit.beforeBlock a i).vertex_monotone huv)
    (f.cut_monotone (Fin.castSucc_le_succ (B.column k)))
    ((Word.ColumnSplit.beforeBlock a i).interval_direction δ u v hd)
    (fun l hl hl' => (f.fiber_direction (B.column k) l hl hl').trans (B.direction_eq k))
  exact ((hs.trans ho).trans
    (WordAction.arrow_obj_heq f (τ.obj d) δ (B.column k) (B.direction_eq k)).symm).trans
      (prefix_direction_before W (τ ⋙ WordAction.functor f) (f.orderHom i) hT d δ k rfl).symm

lemma prefix_outer_arrow :
    HEq ((WordAction.obj (Word.CutFactor.prefixMap f i hi)
      ((prefixDiagram W τ i h).obj d)).arrow (k.castAdd 1))
      (((prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).obj d).arrow
        (k.castAdd 1)) := by
  apply Direction.raw_arrow_heq_of _ _ _ _ _ (Word.append_direction_left _ _ k)
    (Word.append_direction_left _ _ k) ?_ ?_ (prefix_outer_direction W f τ i h hi hT d k)
  · rw [Word.source_left]
    exact prefix_action_vertex W f τ i h hi hT d
      ((Word.ColumnSplit.before b (f.orderHom i)).source k)
  · rw [Word.target_left]
    exact prefix_action_vertex W f τ i h hi hT d
      ((Word.ColumnSplit.before b (f.orderHom i)).target k)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
