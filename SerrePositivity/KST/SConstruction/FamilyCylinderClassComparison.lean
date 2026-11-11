module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositionSquares

/-! # 合成式から構成する端点固定の実円柱比較
概要：同じ両端の元の二円柱が同じ合成を表すとき、端点固定の実二次元円柱を構成する。
方針：指定した全二辺を持つ実三角形を取り、元の三角形を保つ正方形を復号する。
規約：類の等式を raw な円柱の等式とは見なさず、実二次元写像を構成する。
使われ方：実複体の異なる辺路を合成した二円柱の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} [KanComplex E] {f g : U ⟶ E}
  (H K : SSet.Homotopy f g)
  (e : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K))

/-- 指定した元の二円柱と恒等終辺を全三面に持つ実比較三角形。 -/
def familyCylinderClassComparisonTriangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply Nonempty.some
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  change SSet.HomotopyCategory.homMk
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) ≫
      SSet.HomotopyCategory.homMk (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) = _
  rw [SSet.HomotopyCategory.homMk_id, Category.comp_id]
  exact e

/-- 元の両円柱を両面に持つ、全パラメータの実二次元比較。 -/
def familyCylinderClassComparison : SSet.Homotopy H.h K.h where
  h := mappingSquareUncurry
    (endpointFixedEdgeSquare (familyCylinderClassComparisonTriangle H K e))
  h₀ := by
    rw [mappingSquareUncurry_zero, endpointFixedEdgeSquare_zero]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = _
    rw [Equiv.symm_apply_apply, uncurry_curry]
    rfl
  h₁ := by
    rw [mappingSquareUncurry_one, endpointFixedEdgeSquare_one]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry K.h))) = _
    rw [Equiv.symm_apply_apply, uncurry_curry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 比較の始点族は全時刻で厳密に固定される。 -/
lemma familyCylinderClassComparison_source :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyCylinderClassComparison H K e).h = fst U (Δ[1] : SSet.{u}) ≫ f := by
  change _ ≫ mappingSquareUncurry _ = _
  rw [mappingSquareUncurry_source, endpointFixedEdgeSquare_vertical_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 比較の終点族も全時刻で厳密に固定される。 -/
lemma familyCylinderClassComparison_target :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyCylinderClassComparison H K e).h = fst U (Δ[1] : SSet.{u}) ≫ g := by
  change _ ≫ mappingSquareUncurry _ = _
  rw [mappingSquareUncurry_target, endpointFixedEdgeSquare_vertical_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.KST.SConstruction
