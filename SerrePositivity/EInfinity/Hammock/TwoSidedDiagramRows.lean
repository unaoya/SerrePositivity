module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramBar

/-!
# 元の二方向図式の全 bar 行への関手

概要：底と両係数の変更はラベル次数と射列次数を別々に保つ元の bar へ作用する。
方針：元の行の係数射と底の変更を合成する。
規約：barFunctor の作用と同じ元の全単体を保持する。
使われ方：DK10.6(ii)の射列長を固定した部分対角。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory

def rowsFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} ⥤ SimplicialObject SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows (A.left ⋙ nerveFunctor) (A.right ⋙ nerveFunctor)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap (Functor.whiskerRight f.left nerveFunctor)
      (Functor.whiskerRight f.right nerveFunctor) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange.baseChangeRows f.base (_ ⋙ nerveFunctor) (_ ⋙ nerveFunctor)
  map_id A := by ext n k e; rfl
  map_comp f g := by ext n k e; rfl

lemma rowsFunctor_diagonal :
    rowsFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor = barFunctor := rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
