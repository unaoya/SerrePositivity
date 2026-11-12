module

public import SerrePositivity.EInfinity.Hammock.AllMarkedCompositionPoints
public import SerrePositivity.EInfinity.Hammock.RelativeForwardSimplex

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X : Paths C)

def nativeUnitPoint (n : SimplexCategoryᵒᵖ) : (nativeSpace W X X).obj n :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩).app n PUnit.unit

lemma nativeUnitPoint_simplex {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (nativeSpace W X X).map θ (nativeUnitPoint W X n) = nativeUnitPoint W X m :=
  (congrArg (fun k => k PUnit.unit)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩).naturality θ)).symm

lemma inclusion_unitPoint (n : SimplexCategoryᵒᵖ) :
    (inclusion W X X).app n (nativeUnitPoint W X n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X).app n PUnit.unit :=
  Relative.colimitUnit_point (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) ⟨X⟩ n

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
