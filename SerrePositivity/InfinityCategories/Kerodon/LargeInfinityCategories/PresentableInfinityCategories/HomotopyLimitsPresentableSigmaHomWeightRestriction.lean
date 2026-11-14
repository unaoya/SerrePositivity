module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomInfinityBifunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.PresheafHomWeights

/-!
分割で生成：docstring を書き直すこと
概要：元の全自然変換空間族の Yoneda 制限を、元の大きい Yoneda の全族へ比較する。
方針：元の全 Yoneda 宇宙比較を反転・持ち上げし、同じ全共同 Hom と係数制限へ写す。
規約：全 C と全標的係数の自然同型を保持する。
使われ方：両右 Kan 族の元の制限の全自然比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の大きい Yoneda から、元の全 Hom 係数前層への自然変換空間を束ねた全族。 -/
def yonedaHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C))) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 2}

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
