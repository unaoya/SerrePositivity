module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutTripleCollapse
public import SerrePositivity.EInfinity.Hammock.ForwardZigzagDiagramRecovery

/-!
# 圧縮した内部切断と元の中央一列の全図式の一致

概要：内部三列を圧縮した図式を、元の middle の表示変更へ厳密に戻す。
方針：元の列の回収と接合点の自然変換の移送を照合する。
規約：元の前後の接合点と全縦射を保持する。
使われ方：refinedDiagram 全体の圧縮を元の全図式へ戻す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

include h in
lemma middle_word : Word.ColumnSplit.middle w i = Word.single .forward :=
  Word.ColumnSplit.middle_forward w i (column_forward W τ i h)

lemma collapsedColumn_eq_middle :
    collapsedColumnDiagram W τ i h =
      changeWord (middle_word W τ i h) (ColumnSplit.middle i (ofFunctor τ)) := by
  symm
  apply ForwardZigzag.diagram_eq_of_arrow W.paths _ _
    (fun f => (beforeDiagram W τ i).endpoint_right_mem f)
    (fun f => (afterDiagram W τ i).endpoint_left_mem f)
  intro d
  have hm := changeWord_arrow_heq (middle_word W τ i h)
    (ColumnSplit.middle i (ofFunctor τ)) d (0 : Fin 1) (0 : Fin 1) rfl
  have hc := ColumnSplit.middle_arrow i (ofFunctor τ) (d := d)
  change HEq _ ((eqToHom (sourceJoint_eq_rowSource W τ i h)).app d ≫
    (rowColumn W τ i h).app d ≫ (eqToHom (targetJoint_eq_rowTarget W τ i h).symm).app d)
  rw [eqToHom_app, eqToHom_app]
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact hm.trans hc

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
