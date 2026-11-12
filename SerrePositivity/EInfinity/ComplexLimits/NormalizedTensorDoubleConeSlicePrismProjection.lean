module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeSlicePrism
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConePrism

/-!
概要：同じ slice 内の二重 cone prism の全射影は、元の cone prism 自身と厳密に一致する。
方針：同じ join 円柱と同じ大域射影の等式を保持する。
規約：全区間族の等式。使われ方：元の augmentation の全合成三角形の底条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSlicePrism_projection :
    normalizedTensorDoubleConeSlicePrism A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (normalizedTensorConePoint A X) = normalizedTensorConePrism A X Y := by
  simp only [normalizedTensorDoubleConeSlicePrism, normalizedTensorConePrism, Category.assoc,
    normalizedTensorDoubleConeOverJoin_projection]

end SerrePositivity.EInfinity.ComplexLimits
