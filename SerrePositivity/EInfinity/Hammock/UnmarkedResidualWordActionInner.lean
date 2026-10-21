module

public import SerrePositivity.EInfinity.Hammock.UnmarkedResidualInnerSegment
public import SerrePositivity.EInfinity.Hammock.UnmarkedRowCutWordAction
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedPrefix
public import SerrePositivity.EInfinity.Hammock.WordCutFactorBlockCuts
public import SerrePositivity.EInfinity.Hammock.ForwardSegmentColumnTransport
public import SerrePositivity.EInfinity.Hammock.DirectionArrowReflection

/-!
# 元の最小列で切断した残り最初列と語の圧縮

概要：内部切断端点からの最初の一列も元の制限射による作用に一致する。
方針：接合点での区間分割と全行の切断の残りの射列の比較を合成する。
規約：元の全行・同じ生成矢・端点移送を保持する。
使われ方：残りの全図式の語の作用への厳密な比較。
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
lemma residual_inner_action_direction :
    HEq (Direction.arrow .forward
      (WordAction.obj (residualMap f (AttachedPrefix.index W τ h)
        (firstColumn_forward W (τ.obj 0) h))
        ((Attachments.residualDiagram W τ (AttachedPrefix.index W τ h)
          (AttachedPrefix.nonempty W τ h)).obj d))
      ((0 : Fin 1).castAdd
        (Word.ColumnSplit.after b (f.orderHom (AttachedPrefix.index W τ h))).length)
      (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1)))
    (Direction.arrow .forward
      ((Attachments.residualDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d)
      ((0 : Fin 1).castAdd
        (Word.ColumnSplit.after b (f.orderHom (AttachedPrefix.index W τ h))).length)
      (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1))) := by
  let i := AttachedPrefix.index W τ h
  let j := f.orderHom i
  let hi := firstColumn_forward W (τ.obj 0) h
  let hi0 := AttachedPrefix.nonempty W τ h
  let fp := residualMap f i hi
  let c : Fin (residualWord b j).length := (0 : Fin 1).castAdd (Word.ColumnSplit.after b j).length
  let k : Fin ((Word.ColumnSplit.after b j).length + 1) := 0
  let u := residualCutVertex f i k
  let q := (Word.ColumnSplit.afterBlock a i).vertex u
  have hend : q = f.cut j.succ :=
    (residualCutVertex_block f i k).trans (congrArg f.cut
      ((Word.ColumnSplit.afterBlock_vertex b j k).trans (Word.ColumnSplit.afterVertex_zero b j)))
  have hb := (f.fiber_iff j i).2 (show f.orderHom i = j from rfl)
  have hj : b.direction j = .forward := (f.direction_eq i).trans hi
  let hdF := fun l hl hl' => (f.fiber_direction j l hl hl').trans hj
  have hd : ∀ l : Fin a.length, i.castSucc.val ≤ l.val → l.val < q.val →
      a.direction l = .forward := by
    intro l hl hl'
    exact hdF l (by change i.val ≤ l.val at hl; omega) (by rw [hend] at hl'; exact hl')
  have hq : i.val < q.val := by change i.val < i.val + 1 + u.val; omega
  have hc := WordAction.arrow_obj_heq fp ((Attachments.residualDiagram W τ i hi0).obj d)
    .forward c (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1))
  have he := WordAction.segment_heq_of_eq .forward ((Attachments.residualDiagram W τ i hi0).obj d)
    fp.cut_zero (residual_cut_eq f i hi k) (fp.cut_monotone (Fin.castSucc_le_succ c))
    (Fin.zero_le _) (fun l hl hl' => (fp.fiber_direction c l hl hl').trans
      (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1)))
    (Attachments.residual_inner_direction i u hd)
  have hs := (hc.trans he).trans (Attachments.residual_inner_segment W τ i hi0 d u hd)
  have hn := Segment.fromColumn_heq (τ.obj d) i.castSucc q (f.cut j.castSucc) (f.cut j.succ)
    hd hdF i (show i.castSucc.val ≤ i.val from le_rfl) hq hb.1 hb.2 hend
  have hprod := heq_comp rfl rfl (congrArg (τ.obj d).vertex hend)
    (HEq.rfl : HEq ((rowResidual W τ i hi0).app d) ((rowResidual W τ i hi0).app d)) hn
  exact ((hs.trans hprod).trans (row_cut_right W f τ h hT d).symm).trans
    (Attachments.residual_inner_arrow W (τ ⋙ WordAction.functor f) j hT d).symm

include hT in
lemma residual_inner_action_arrow :
    HEq ((WordAction.obj
      (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      ((Attachments.residualDiagram W τ (AttachedPrefix.index W τ h)
          (AttachedPrefix.nonempty W τ h)).obj d)).arrow
        ((0 : Fin 1).castAdd
        (Word.ColumnSplit.after b (f.orderHom (AttachedPrefix.index W τ h))).length))
      (((Attachments.residualDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d).arrow
        ((0 : Fin 1).castAdd
        (Word.ColumnSplit.after b (f.orderHom (AttachedPrefix.index W τ h))).length)) := by
  apply Direction.raw_arrow_heq_of _ _ .forward _ _
    (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1))
    (Word.append_direction_left (Word.single .forward) _ (0 : Fin 1))
    (residual_vertices W f τ h hT d _) (residual_vertices W f τ h hT d _)
    (residual_inner_action_direction W f τ h hT d)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
