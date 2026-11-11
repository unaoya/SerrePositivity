module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixInnerSegment
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowCutWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorBlockCuts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentColumnTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowReflection

/-!
# 元の最小列で切断した prefix 最終列と語の圧縮

概要：内部切断端点までの最後の一列も元の制限射による作用に一致する。
方針：接合点での区間分割と全行の切断の接頭射の比較を合成する。
規約：元の全行・同じ生成矢・端点移送を保持する。
使われ方：prefix 全図式の語の作用への厳密な比較。

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
lemma prefix_inner_action_direction :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h).obj d))
      ((0 : Fin 1).natAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d)
      ((0 : Fin 1).natAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1))) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h
  let j := f.orderHom i
  let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h
  let hi0 := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h
  let fp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi
  let c : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b j).length := (0 : Fin 1).natAdd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b j).length
  let k := Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b j).length
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex f i k
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock a i).vertex u
  have hstart : p = f.cut j.castSucc :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex_block f i k).trans (congrArg f.cut
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex b j k).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex_last b j)))
  have hb := (f.fiber_iff j i).2 (show f.orderHom i = j from rfl)
  have hj : b.direction j = .forward := (f.direction_eq i).trans hi
  let hdF := fun l hl hl' => (f.fiber_direction j l hl hl').trans hj
  have hd : ∀ l : Fin a.length, p.val ≤ l.val → l.val < i.succ.val →
      a.direction l = .forward := by
    intro l hl hl'
    exact hdF l (by rw [hstart] at hl; exact hl)
      (by change l.val < i.val + 1 at hl'; omega)
  have hp : p.val ≤ i.val := by rw [hstart]; exact hb.1
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq fp ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i hi0).obj d)
    .forward c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1))
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq .forward ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i hi0).obj d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_cut_eq f i hi k) fp.cut_last (fp.cut_monotone (Fin.castSucc_le_succ c))
    (Fin.le_last _) (fun l hl hl' => (fp.fiber_direction c l hl hl').trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_inner_direction i u hd)
  have hs := (hc.trans he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_inner_segment W τ i hi0 d u hd)
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn_heq (τ.obj d) p i.succ (f.cut j.castSucc) (f.cut j.succ)
    hd hdF i hp (by change i.val < i.val + 1; omega) hb.1 hb.2 hstart
  have hprod := heq_comp (congrArg (τ.obj d).vertex hstart) rfl rfl hn
    (HEq.rfl : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i hi0).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i hi0).app d))
  exact ((hs.trans hprod).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.row_cut_left W f τ h hT d).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_inner_arrow W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) j hT d).symm

include hT in
lemma prefix_inner_action_arrow :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h).obj d)).arrow
        ((0 : Fin 1).natAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d).arrow
        ((0 : Fin 1).natAdd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of _ _ .forward _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (0 : Fin 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertices W f τ h hT d _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertices W f τ h hT d _)
    (prefix_inner_action_direction W f τ h hT d)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
