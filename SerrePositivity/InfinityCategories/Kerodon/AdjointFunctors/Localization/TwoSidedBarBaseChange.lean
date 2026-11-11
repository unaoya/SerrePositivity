module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElementsBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar

/-!
# 元の二方向 bar の底の関手による比較

概要：底の関手は元の二方向 bar の全行と同じ対角の比較射を与える。
方針：元の要素圏の比較を各次数で nerve に送り、同じ対角関手を使う。
規約：元の底の全射と両ラベルを保持し、弱同値性は仮定しない。
使われ方：DK9.5と10.5の元の底の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange
open CategoryTheory Opposite

variable {V W : Type u} [Category.{u} V] [Category.{u} W]
  (H : V ⥤ W) (F : Wᵒᵖ ⥤ SSet.{u}) (G : W ⥤ SSet.{u})

def baseChangeRows : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows (H.op ⋙ F) (H ⋙ G) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows F G where
  app n := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre H (F.flip.obj n) (G.flip.obj n))
  naturality {n m} θ := by
    ext k e
    exact congrArg (fun J => e ⋙ J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre_naturality H (F.flip.map θ) (G.flip.map θ)).symm

def baseChange : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (H.op ⋙ F) (H ⋙ G) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (baseChangeRows H F G)

variable {F G} {F' : Wᵒᵖ ⥤ SSet.{u}} {G' : W ⥤ SSet.{u}}

lemma baseChange_map (α : F ⟶ F') (β : G ⟶ G') :
    baseChange H F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map α β =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map (Functor.whiskerLeft H.op α) (Functor.whiskerLeft H β) ≫ baseChange H F' G' := by
  ext n e
  exact congrArg (fun J => e ⋙ J)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre_naturality H
      (((flipFunctor _ _ _).map α).app n) (((flipFunctor _ _ _).map β).app n))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange
