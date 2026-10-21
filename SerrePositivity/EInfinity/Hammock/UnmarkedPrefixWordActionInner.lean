module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPrefixInnerSegment
public import SerrePositivity.EInfinity.Hammock.UnmarkedRowCutWordAction
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedPrefix
public import SerrePositivity.EInfinity.Hammock.WordCutFactorBlockCuts
public import SerrePositivity.EInfinity.Hammock.ForwardSegmentColumnTransport
public import SerrePositivity.EInfinity.Hammock.DirectionArrowReflection

/-!
# 元の最小列で切断した prefix 最終列と語の圧縮

概要：内部切断端点までの最後の一列も元の制限射による作用に一致する。
方針：接合点での区間分割と全行の切断の接頭射の比較を合成する。
規約：元の全行・同じ生成矢・端点移送を保持する。
使われ方：prefix 全図式の語の作用への厳密な比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n)
  (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (AttachedPrefix.index W τ h)) ≠ []) (d : Fin (n.unop.len + 1))

include hT in
lemma prefix_inner_action_direction :
    HEq (Direction.arrow .forward
      (WordAction.obj (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
        ((AttachedPrefix.diagram W τ h).obj d))
      ((0 : Fin 1).natAdd
        (Word.ColumnSplit.before b (f.orderHom (AttachedPrefix.index W τ h))).length)
      (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1)))
    (Direction.arrow .forward
      ((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d)
      ((0 : Fin 1).natAdd
        (Word.ColumnSplit.before b (f.orderHom (AttachedPrefix.index W τ h))).length)
      (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1))) := by
  let i := AttachedPrefix.index W τ h
  let j := f.orderHom i
  let hi := firstColumn_forward W (τ.obj 0) h
  let hi0 := AttachedPrefix.nonempty W τ h
  let fp := prefixMap f i hi
  let c : Fin (prefixWord b j).length := (0 : Fin 1).natAdd (Word.ColumnSplit.before b j).length
  let k := Fin.last (Word.ColumnSplit.before b j).length
  let u := prefixCutVertex f i k
  let p := (Word.ColumnSplit.beforeBlock a i).vertex u
  have hstart : p = f.cut j.castSucc :=
    (prefixCutVertex_block f i k).trans (congrArg f.cut
      ((Word.ColumnSplit.beforeBlock_vertex b j k).trans (Word.ColumnSplit.beforeVertex_last b j)))
  have hb := (f.fiber_iff j i).2 (show f.orderHom i = j from rfl)
  have hj : b.direction j = .forward := (f.direction_eq i).trans hi
  let hdF := fun l hl hl' => (f.fiber_direction j l hl hl').trans hj
  have hd : ∀ l : Fin a.length, p.val ≤ l.val → l.val < i.succ.val →
      a.direction l = .forward := by
    intro l hl hl'
    exact hdF l (by rw [hstart] at hl; exact hl)
      (by change l.val < i.val + 1 at hl'; omega)
  have hp : p.val ≤ i.val := by rw [hstart]; exact hb.1
  have hc := WordAction.arrow_obj_heq fp ((Attachments.prefixDiagram W τ i hi0).obj d)
    .forward c (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1))
  have he := WordAction.segment_heq_of_eq .forward ((Attachments.prefixDiagram W τ i hi0).obj d)
    (prefix_cut_eq f i hi k) fp.cut_last (fp.cut_monotone (Fin.castSucc_le_succ c))
    (Fin.le_last _) (fun l hl hl' => (fp.fiber_direction c l hl hl').trans
      (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1)))
    (Attachments.prefix_inner_direction i u hd)
  have hs := (hc.trans he).trans (Attachments.prefix_inner_segment W τ i hi0 d u hd)
  have hn := Segment.toColumn_heq (τ.obj d) p i.succ (f.cut j.castSucc) (f.cut j.succ)
    hd hdF i hp (by change i.val < i.val + 1; omega) hb.1 hb.2 hstart
  have hprod := heq_comp (congrArg (τ.obj d).vertex hstart) rfl rfl hn
    (HEq.rfl : HEq ((rowPrefix W τ i hi0).app d) ((rowPrefix W τ i hi0).app d))
  exact ((hs.trans hprod).trans (row_cut_left W f τ h hT d).symm).trans
    (Attachments.prefix_inner_arrow W (τ ⋙ WordAction.functor f) j hT d).symm

include hT in
lemma prefix_inner_action_arrow :
    HEq ((WordAction.obj
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      ((AttachedPrefix.diagram W τ h).obj d)).arrow
        ((0 : Fin 1).natAdd
        (Word.ColumnSplit.before b (f.orderHom (AttachedPrefix.index W τ h))).length))
      (((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d).arrow
        ((0 : Fin 1).natAdd
        (Word.ColumnSplit.before b (f.orderHom (AttachedPrefix.index W τ h))).length)) := by
  apply Direction.raw_arrow_heq_of _ _ .forward _ _
    (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1))
    (Word.append_direction_right _ (Word.single .forward) (0 : Fin 1))
    (prefix_vertices W f τ h hT d _) (prefix_vertices W f τ h hT d _)
    (prefix_inner_action_direction W f τ h hT d)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
