module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnReverseHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap

/-!
# 元の混合二方向の一点係数の比較

概要：元の右係数の対角比較は同じ一点係数の恒等射である。
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
open CategoryTheory SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeReverseFirstRightSpaceMap :=
  rightSpaceMap (freeFirstMarkedObjectEquiv C) (freeReverseFirstTargetObjectEquiv C w X Y)
    (freeReverseFirstMarkedObjectEquiv_naturality C w X Y)
    (freeReverseFirstTargetObjectEquiv_naturality C w X Y) (freeBackwardForwardAugmentation C w X Y)
    (freeReverseFirstMarkedObjectEquiv_augmentation C w X Y) Z
lemma freeReverseFirstRightSpaceMap_eq_id : freeReverseFirstRightSpaceMap C w X Y Z = 𝟙 _ := by
  ext n σ
  rfl
lemma freeReverseFirstRightSpaceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeReverseFirstRightSpaceMap C w X Y Z) := by
  rw [freeReverseFirstRightSpaceMap_eq_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
end SerrePositivity.EInfinity.Hammock.FirstColumn
