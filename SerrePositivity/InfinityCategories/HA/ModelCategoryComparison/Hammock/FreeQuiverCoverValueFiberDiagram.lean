module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCoverNerveFiber

/-!
# 元の全語の graph の fiber と nerve の図式の同型

概要：各語の元の fiber の同定は全語の作用にも自然である。
方針：元の全部分圏の包含と同じ単体を回収する。
規約：元の全語と全単体作用素の二方向を同時に保持する。
使われ方：元の hammock 上の値の fiber への余極限比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
open _root_.CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def fiberValueDiagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.fiberDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValueLabels A Y) β :=
  NatIso.ofComponents (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphIso A Y β) (by
    intro a b f
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    rfl)

lemma fiberValueDiagramIso_hom_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberValueDiagramIso A Y β).hom.app w ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w) β =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
