module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeFirstColumnMixedHomWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramVertexCoefficientMap

/-!
# 元の混合二方向の一点係数の比較

概要：元の左係数の対角比較は同じ一点係数の恒等射である。
方針：全単体で元の定値係数の作用を計算する。
規約：一点係数の弱同値性を追加入力にしない。
使われ方：DK10.4–10.6の元の混合二方向への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeMixedFirstLeftSpaceMap :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpaceMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstTargetObjectEquiv C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstMarkedObjectEquiv_naturality C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstTargetObjectEquiv_naturality C w X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardBackwardAugmentation C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstMarkedObjectEquiv_augmentation C w X Y) Z
lemma freeMixedFirstLeftSpaceMap_eq_id : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstLeftSpaceMap C w X Y Z = 𝟙 _ := by
  ext n σ
  rfl
lemma freeMixedFirstLeftSpaceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstLeftSpaceMap C w X Y Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeMixedFirstLeftSpaceMap_eq_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
