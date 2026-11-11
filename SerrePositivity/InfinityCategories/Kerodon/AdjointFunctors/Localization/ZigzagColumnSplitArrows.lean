module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplitBlocks

/-!
# 前後の切断図式の元の全列の回収

概要：元の前後の語から切り出した全列を、元の同じ列へ異種等式で照合する。
方針：部分図式の端点移送を除き、元の語の表示変更を回収する。
規約：元の全行と前後の元の列番号を保持する。
使われ方：前後の連続部分の元の区間合成との比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

lemma before_arrow (d : D) (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).obj d).arrow j)
      ((F.obj d).arrow ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w p).column j)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ (by
    change 0 + j.val = j.val
    omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_arrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_arrow)


lemma after_arrow (d : D) (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).obj d).arrow j)
      ((F.obj d).arrow ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w p).column j)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ (by
    change p.val + 1 + j.val = p.val + 1 + j.val
    rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after_arrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (after_arrow)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
