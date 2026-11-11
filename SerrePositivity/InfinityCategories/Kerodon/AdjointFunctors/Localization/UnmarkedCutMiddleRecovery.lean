module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutTripleCollapse
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagramRecovery

/-!
# 圧縮した内部切断と元の中央一列の全図式の一致

概要：内部三列を圧縮した図式を、元の middle の表示変更へ厳密に戻す。
方針：元の列の回収と接合点の自然変換の移送を照合する。
規約：元の前後の接合点と全縦射を保持する。
使われ方：refinedDiagram 全体の圧縮を元の全図式へ戻す。

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
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

include h in
lemma middle_word : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.middle_forward w i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.column_forward W τ i h)

lemma collapsedColumn_eq_middle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapsedColumnDiagram W τ i h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (middle_word W τ i h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)) := by
  symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_eq_of_arrow W.paths _ _
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem f)
  intro d
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (middle_word W τ i h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)) d (0 : Fin 1) (0 : Fin 1) rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.middle_arrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ) (d := d)
  change HEq _ ((eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint_eq_rowSource W τ i h)).app d ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W τ i h).app d ≫ (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint_eq_rowTarget W τ i h).symm).app d)
  rw [eqToHom_app, eqToHom_app]
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact hm.trans hc

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
