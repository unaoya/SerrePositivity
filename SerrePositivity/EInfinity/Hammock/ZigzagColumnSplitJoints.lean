module

public import SerrePositivity.EInfinity.Hammock.ZigzagColumnSplitRecovery

/-!
# 任意列の前後の図式の接合点を元の両端へ照合する

概要：前後の図式の接合点関手は、元の列の左右の頂点評価と厳密に一致する。
方針：元の頂点と全縦成分の回収を関手の外延性へ渡す。
規約：対象だけでなく元の全射の一致を証明する。
使われ方：内部の切断の自然変換を前後の全語へ接続する。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : MovingDiagram D C W w A B)

def sourceJoint : D ⥤ C := (expanded p F).leftPart.jointFunctor

def targetJoint : D ⥤ C := (expanded p F).jointFunctor

lemma sourceJoint_eq : sourceJoint p F = F.evaluation p.castSucc := by
  apply CategoryTheory.Functor.ext (fun d =>
    (before_vertex p F d (Fin.last (Word.ColumnSplit.before w p).length)).trans
      (congrArg (F.obj d).vertex (Word.ColumnSplit.beforeVertex_last w p))) ?_
  intro d e f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact (before_map_app p F f (Fin.last (Word.ColumnSplit.before w p).length)).trans
    (Zigzag.MovingHom.app_heq (F.map f) (Word.ColumnSplit.beforeVertex_last w p))

lemma targetJoint_eq : targetJoint p F = F.evaluation p.succ := by
  apply CategoryTheory.Functor.ext (fun d =>
    (after_vertex p F d 0).trans
      (congrArg (F.obj d).vertex (Word.ColumnSplit.afterVertex_zero w p))) ?_
  intro d e f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact (after_map_app p F f 0).trans
    (Zigzag.MovingHom.app_heq (F.map f) (Word.ColumnSplit.afterVertex_zero w p))

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit
