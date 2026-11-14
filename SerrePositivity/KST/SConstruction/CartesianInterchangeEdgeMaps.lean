module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CartesianInterchangeDiamond
public import SerrePositivity.KST.SConstruction.MappingSquareCornerIdentities

/-! # 実交換三角形対の四辺の全区間写像
概要：元の二辺の実交換三角形対から四辺を回収し、元の全区間と固定頂点で表示する。
方針：直積辺の米田表示と恒等辺の定数表示を同じ実写像へ移す。
規約：四辺の端点だけでなく全一単体の実写像を厳密に保持する。
使われ方：三入力の交換面を、実際の BF whisker と raw 補正の全辺へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K L M : SSet.{u}} {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌}
  (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M)

/-- 元の直積辺の全区間写像は、元の同じ両区間写像の射対。 -/
lemma cartesianEdgePair_map :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e f).edge =
      lift (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm f.edge) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (e.edge, f.edge) =
    (SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge),
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm f.edge))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 第一経路下辺の全区間は、元の第一辺と元の第二始点の同じ合成。 -/
lemma cartesianInterchangeFirstLower_map :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeFirstLower e f p).edge =
      lift (SSet.yonedaEquiv.symm e.edge) (SSet.const y₀) ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeFirstLower, SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp,
    cartesianEdgePair_map, mappingIdentityEdge_map]

/-- 第一経路上辺の全区間は、元の第一終点と元の第二辺の同じ合成。 -/
lemma cartesianInterchangeFirstUpper_map :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeFirstUpper e f p).edge =
      lift (SSet.const x₁) (SSet.yonedaEquiv.symm f.edge) ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeFirstUpper, SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp,
    cartesianEdgePair_map, mappingIdentityEdge_map]

/-- 第二経路下辺の全区間は、元の第一始点と元の第二辺の同じ合成。 -/
lemma cartesianInterchangeSecondLower_map :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeSecondLower e f p).edge =
      lift (SSet.const x₀) (SSet.yonedaEquiv.symm f.edge) ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeSecondLower, SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp,
    cartesianEdgePair_map, mappingIdentityEdge_map]

/-- 第二経路上辺の全区間は、元の第一辺と元の第二終点の同じ合成。 -/
lemma cartesianInterchangeSecondUpper_map :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeSecondUpper e f p).edge =
      lift (SSet.yonedaEquiv.symm e.edge) (SSet.const y₁) ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianInterchangeSecondUpper, SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp,
    cartesianEdgePair_map, mappingIdentityEdge_map]

end SerrePositivity.KST.SConstruction
