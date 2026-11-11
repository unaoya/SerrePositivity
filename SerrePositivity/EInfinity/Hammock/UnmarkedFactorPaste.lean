module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
public import SerrePositivity.EInfinity.Hammock.AllMarkedNative

/-!
# 同じ指定 prefix・生成矢・残りからの元の hammock への貼り戻し

概要：元の三因子を既存の hammock 合成で接続する単体写像を構成する。
方針：指定部分圏の元の包含と同じ生成射の一定単体を使う。
規約：実際の二つの余極限の点と元の生成矢を保持する。
使われ方：反復切断の貼り戻しと抽出との両逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)
  {n m : SimplexCategoryᵒᵖ}

def pastePoint (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n) (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.right Y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.left g.val.right ((AllMarked.inclusion W X g.val.left).app n p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n)) r

lemma pastePoint_simplex (θ : n ⟶ m) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) :
    pastePoint W X Y g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).map θ r) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ (pastePoint W X Y g p r) := by
  have hp := congrArg (fun k => k p) ((AllMarked.inclusion W X g.val.left).naturality θ)
  have hi := (congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.left g.val.right) hp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_simplex W.paths θ g.val.hom.toPath).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_simplex W.paths X g.val.left g.val.right θ
        ((AllMarked.inclusion W X g.val.left).app n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n))
  exact (congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.right Y) hi rfl).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_simplex W.paths X g.val.right Y θ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.left g.val.right ((AllMarked.inclusion W X g.val.left).app n p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n)) r)

def paste : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y where
  app _ := ↾fun s => pastePoint W X Y s.1 s.2.1 s.2.2
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact pastePoint_simplex W X Y θ s.1 s.2.1 s.2.2

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
