module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitRecovery

/-!
# 任意列の前後の図式の接合点を元の両端へ照合する

概要：前後の図式の接合点関手は、元の列の左右の頂点評価と厳密に一致する。
方針：元の頂点と全縦成分の回収を関手の外延性へ渡す。
規約：対象だけでなく元の全射の一致を証明する。
使われ方：内部の切断の自然変換を前後の全語へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

def sourceJoint : D ⥤ C := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.expanded p F).leftPart.jointFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.sourceJoint export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints (sourceJoint)


def targetJoint : D ⥤ C := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.expanded p F).jointFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.targetJoint export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints (targetJoint)


lemma sourceJoint_eq : sourceJoint p F = F.evaluation p.castSucc := by
  apply CategoryTheory.Functor.ext (fun d =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_vertex p F d (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length)).trans
      (congrArg (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex_last w p))) ?_
  intro d e f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_map_app p F f (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex_last w p))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.sourceJoint_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints (sourceJoint_eq)


lemma targetJoint_eq : targetJoint p F = F.evaluation p.succ := by
  apply CategoryTheory.Functor.ext (fun d =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.after_vertex p F d 0).trans
      (congrArg (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex_zero w p))) ?_
  intro d e f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.after_map_app p F f 0).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex_zero w p))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.targetJoint_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints (targetJoint_eq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints
