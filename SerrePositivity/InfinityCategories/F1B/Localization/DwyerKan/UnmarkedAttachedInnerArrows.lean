module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendDirections

/-!
# 内部接続列の元の接頭射・残りへの回収

概要：prefix 最終列と残り最初列を、元の切断の前後の射列へ戻す。
方針：方向付きの連結列と接続自然変換の端点移送を取り除く。
規約：元の射列と元の生成矢の端点を保持する。
使われ方：接合点で分割した区間合成の内部列の照合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1))

lemma prefix_inner_arrow :
    HEq (Direction.arrow .forward ((prefixDiagram W τ i h).obj d)
      ((0 : Fin 1).natAdd (Word.ColumnSplit.before w i).length)
      (Word.append_direction_right (Word.ColumnSplit.before w i)
        (Word.single .forward) (0 : Fin 1))) ((rowPrefix W τ i h).app d) := by
  apply HEq.trans (ZigzagAppend.direction_right_heq ((beforeDiagram W τ i).obj d)
    ((leftBlock W τ i h).obj d) .forward (0 : Fin 1) rfl)
  change HEq (eqToHom _ ≫ (leftAttachment W τ i h).app d ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  change HEq ((eqToHom (sourceJoint_eq_rowSource W τ i h)).app d ≫
    (rowPrefix W τ i h).app d) _
  rw [eqToHom_app]
  simp only [eqToHom_comp_heq_iff]
  rfl

lemma residual_inner_arrow :
    HEq (Direction.arrow .forward ((residualDiagram W τ i h).obj d)
      ((0 : Fin 1).castAdd (Word.ColumnSplit.after w i).length)
      (Word.append_direction_left (Word.single .forward)
        (Word.ColumnSplit.after w i) (0 : Fin 1))) ((rowResidual W τ i h).app d) := by
  apply HEq.trans (ZigzagAppend.direction_left_heq ((rightBlock W τ i h).obj d)
    ((afterDiagram W τ i).obj d) .forward (0 : Fin 1) rfl)
  change HEq (eqToHom _ ≫ (rightAttachment W τ i h).app d ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  change HEq ((rowResidual W τ i h).app d ≫
    (eqToHom (targetJoint_eq_rowTarget W τ i h).symm).app d) _
  rw [eqToHom_app]
  simp only [comp_eqToHom_heq_iff]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
