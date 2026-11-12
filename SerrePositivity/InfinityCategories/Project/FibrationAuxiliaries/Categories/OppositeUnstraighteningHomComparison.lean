module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.CommonWeightedNativeHomAction
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.CommonWeightedNativePrismComparison

/-!
概要：元の全相対 Hom 上で、反転 unstraightening の二つの実際の作用を関手同型で結ぶ。
方針：構成した共通 weighted 始域の native prism の両端と底を渡し、元の全 Hom へ降下する。
規約：prism の存在や端点条件を追加仮定として受け取らない。
使われ方：実際の straightening の写像空間作用と既存の比較同値の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の全 Hom 上の二つの実際の unstraightening 作用は、追加条件なしで関手同型を持つ。 -/
def oppositeUnstraighteningHomComparisonIso {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeUnstraighteningHomRight F G) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeUnstraighteningHomLeft F G) :=
  _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.oppositeUnstraighteningHomComparisonIsoOfNativePrism F G
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.commonWeightedNativePointedPrism F G)
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.commonWeightedNativePointedPrism_zero F G)
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.commonWeightedNativePointedPrism_one_eq F G)
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.commonWeightedNativePointedPrism_projection F G)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
