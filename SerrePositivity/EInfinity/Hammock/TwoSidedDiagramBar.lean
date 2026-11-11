module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramTotal

/-!
# 元の二方向図式から bar への関手と Thomason 自然変換

概要：元の bar の全作用素を束ね、元の全圏の nerve への自然変換を得る。
方針：同じ係数射と底の変更の比較を全単体で保持する。
規約：Thomason の自然性は元の射の厳密な正方形。
使われ方：DK10.6の全次数の対角比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory Opposite

def barFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} ⥤ SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (A.left ⋙ nerveFunctor) (A.right ⋙ nerveFunctor)
  map f := TwoSidedThomason.transitionBar f.base f.left f.right
  map_id A := by
    ext n e
    rfl
  map_comp f g := by
    ext n e
    rfl

def thomasonMap : barFunctor ⟶ totalFunctor ⋙ nerveFunctor where
  app A := TwoSidedThomason.map A.left A.right
  naturality _ _ f := (TwoSidedThomason.map_transition f.base f.left f.right).symm

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
