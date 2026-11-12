module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorValue

/-!
# 切断因子の依存和の元の非指定文字列

概要：同じ生成矢の一文字と残りの元の文字列を連結する単体写像を構成する。
方針：残りの既存の colimitValue の自然性を使う。
規約：元の生成矢と元の残りの余極限を使う。
使われ方：元の非空部分上の切断の文字列回収と長さの減少。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def wordValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) where
  app n := ↾fun s => s.1.val :: (colimitValue W s.1.val.right Y).app n s.2.2
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg (List.cons s.1.val) (congrArg (fun k => k s.2.2)
      ((colimitValue W s.1.val.right Y).naturality θ))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
