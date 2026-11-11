module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedResidualInnerSegment
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowCutWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorBlockCuts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentColumnTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowReflection

/-!
# 元の最小列で切断した残り最初列と語の圧縮

概要：内部切断端点からの最初の一列も元の制限射による作用に一致する。
方針：接合点での区間分割と全行の切断の残りの射列の比較を合成する。
規約：元の全行・同じ生成矢・端点移送を保持する。
使われ方：残りの全図式の語の作用への厳密な比較。

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
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n)
  (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) ≠ []) (d : Fin (n.unop.len + 1))

include hT in
lemma residual_inner_action_direction :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d))
      ((0 : Fin 1).castAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d)
      ((0 : Fin 1).castAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1))) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h
  let j := f.orderHom i
  let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h
  let hi0 := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h
  let fp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi
  let c : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b j).length := (0 : Fin 1).castAdd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b j).length
  let k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b j).length + 1) := 0
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k
  let q := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock a i).vertex u
  have hend : q = f.cut j.succ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_block f i k).trans (congrArg f.cut
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex b j k).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex_zero b j)))
  have hb := (f.fiber_iff j i).2 (show f.orderHom i = j from rfl)
  have hj : b.direction j = .forward := (f.direction_eq i).trans hi
  let hdF := fun l hl hl' => (f.fiber_direction j l hl hl').trans hj
  have hd : ∀ l : Fin a.length, i.castSucc.val ≤ l.val → l.val < q.val →
      a.direction l = .forward := by
    intro l hl hl'
    exact hdF l (by change i.val ≤ l.val at hl; omega) (by rw [hend] at hl'; exact hl')
  have hq : i.val < q.val := by change i.val < i.val + 1 + u.val; omega
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq fp ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i hi0).obj d)
    .forward c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1))
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq .forward ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i hi0).obj d)
    fp.cut_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq f i hi k) (fp.cut_monotone (Fin.castSucc_le_succ c))
    (Fin.zero_le _) (fun l hl hl' => (fp.fiber_direction c l hl hl').trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_inner_direction i u hd)
  have hs := (hc.trans he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_inner_segment W τ i hi0 d u hd)
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn_heq (τ.obj d) i.castSucc q (f.cut j.castSucc) (f.cut j.succ)
    hd hdF i (show i.castSucc.val ≤ i.val from le_rfl) hq hb.1 hb.2 hend
  have hprod := heq_comp rfl rfl (congrArg (τ.obj d).vertex hend)
    (HEq.rfl : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i hi0).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i hi0).app d)) hn
  exact ((hs.trans hprod).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.row_cut_right W f τ h hT d).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_inner_arrow W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) j hT d).symm

include hT in
lemma residual_inner_action_arrow :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d)).arrow
        ((0 : Fin 1).castAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d).arrow
        ((0 : Fin 1).castAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of _ _ .forward _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _ (0 : Fin 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertices W f τ h hT d _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertices W f τ h hT d _)
    (residual_inner_action_direction W f τ h hT d)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
