module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositionSquares

/-! # 指定した実三角形からの端点固定二次元円柱
概要：元の二円柱を二面に持つ指定実三角形を、そのまま端点固定比較にする。
方針：同じ三角形を保持する正方形を uncurry し、全四面を回収する。
規約：三角形も円柱も選び直さず、元の実二単体全体を保持する。
使われ方：四つの元の三角形から得た比較を元のパラメータへ戻す。
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
variable {U E : SSet.{u}} {a b : U ⟶ E} {H K : SSet.Homotopy a b}
  (t : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)))

/-- 指定した同じ実三角形を保つ、元の二円柱の端点固定二次元比較。 -/
def familyCylinderTriangleComparison : SSet.Homotopy H.h K.h where
  h := mappingSquareUncurry (endpointFixedEdgeSquare t)
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

/-- 元の始点族は全比較時刻で厳密に固定される。 -/
lemma familyCylinderTriangleComparison_source :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyCylinderTriangleComparison t).h = fst U (Δ[1] : SSet.{u}) ≫ a := by
  change _ ≫ mappingSquareUncurry _ = _
  rw [mappingSquareUncurry_source, endpointFixedEdgeSquare_vertical_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 元の終点族も全比較時刻で厳密に固定される。 -/
lemma familyCylinderTriangleComparison_target :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyCylinderTriangleComparison t).h = fst U (Δ[1] : SSet.{u}) ≫ b := by
  change _ ≫ mappingSquareUncurry _ = _
  rw [mappingSquareUncurry_target, endpointFixedEdgeSquare_vertical_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.KST.SConstruction
