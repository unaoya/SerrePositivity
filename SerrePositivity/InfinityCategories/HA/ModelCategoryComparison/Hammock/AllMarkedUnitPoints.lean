module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedCompositionPoints
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeForwardSimplex

/-!
# 元の指定 hammock の単位点と包含の単位保存

概要：指定部分圏自身の空語の単位点と元の包含による回収を固定する。
方針：元の単体的単位と相対関手の単位保存を代入する。
規約：元の指定部分圏内の点を使う。
使われ方：全因子列の単位を指定終端として構成する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X : Paths C)

def nativeUnitPoint (n : SimplexCategoryᵒᵖ) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X X).obj n :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩).app n PUnit.unit

lemma nativeUnitPoint_simplex {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X X).map θ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeUnitPoint W X n) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeUnitPoint W X m :=
  (congrArg (fun k => k PUnit.unit)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩).naturality θ)).symm

lemma inclusion_unitPoint (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X X).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeUnitPoint W X n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X).app n PUnit.unit :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitUnit_point (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) ⟨X⟩ n

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
