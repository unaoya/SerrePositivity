module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquare

/-!
概要：同じ輸送四角形を、元の四辺を保って任意の係数射で制限する。
方針：二つの区間を固定して全パラメーターだけを前合成する。
規約：底の四角形と指定された四面を保持する。
使われ方：動く始点と二つの Kan 射の全族に対する合成輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
/-- 概要：全係数の制限後も同じ四つの区間境界を保持する。
方針：区間端点の自然性で四面を回収する。規約：指定四角形を保持。使われ方：合成輸送。 -/
def TransportIntervalSquare.precomp {B P Q : SSet.{u}} {a b c d : B _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportIntervalSquare P a b c d) (q : Q ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportIntervalSquare Q a b c d where
  bottom := q ≫ s.bottom
  top := q ≫ s.top
  left := q ≫ s.left
  right := q ≫ s.right
  square := (Δ[1] ◁ (Δ[1] ◁ q)) ≫ s.square
  zero := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, s.zero,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  one := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, s.one,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  inner_zero := by
    rw [← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, whiskerLeft_comp,
      Category.assoc, s.inner_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  inner_one := by
    rw [← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, whiskerLeft_comp,
      Category.assoc, s.inner_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
