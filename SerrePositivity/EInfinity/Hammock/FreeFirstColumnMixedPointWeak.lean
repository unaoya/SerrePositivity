module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnMixedHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap

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
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeMixedFirstLeftSpaceMap :=
  leftSpaceMap (freeFirstMarkedObjectEquiv C) (freeMixedFirstTargetObjectEquiv C w X Y)
    (freeMixedFirstMarkedObjectEquiv_naturality C w X Y)
    (freeMixedFirstTargetObjectEquiv_naturality C w X Y) (freeForwardBackwardAugmentation C w X Y)
    (freeMixedFirstMarkedObjectEquiv_augmentation C w X Y) Z
lemma freeMixedFirstLeftSpaceMap_eq_id : freeMixedFirstLeftSpaceMap C w X Y Z = 𝟙 _ := by
  ext n σ
  rfl
lemma freeMixedFirstLeftSpaceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeMixedFirstLeftSpaceMap C w X Y Z) := by
  rw [freeMixedFirstLeftSpaceMap_eq_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
end SerrePositivity.EInfinity.Hammock.FirstColumn
