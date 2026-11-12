module
public import SerrePositivity.KST.SConstruction.ConstantDiamondVertexTransport

/-! # 定数三辺の元の二三角形から第四辺の端点固定比較
概要：三辺と指定辺が定数なら、生成第四辺への全端点固定比較を実構成する。
方針：同じ元の二三角形の表示移送を、固定境界 Kan 写像空間の実 span 比較へ渡す。
規約：元の両全三角形を同じ高次比較の指定面に保持する。全境界の任意充填は使わない。
使われ方：第四辺 raw 比較の零段を、元の全二単体の射影から実構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] {x m n z : E _⦋0⦌}
  {a : E.Edge x m} {b : E.Edge m z} {c e : E.Edge x n} {d : E.Edge n z}
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c d)
  (ha : ∃ v, SSet.yonedaEquiv.symm a.edge = SSet.const v)
  (hb : ∃ v, SSet.yonedaEquiv.symm b.edge = SSet.const v)
  (hd : ∃ v, SSet.yonedaEquiv.symm d.edge = SSet.const v)
  (he : ∃ v, SSet.yonedaEquiv.symm e.edge = SSet.const v)

/-- 元の指定定数辺から生成第四辺への、同じ元の二三角形を使う全端点固定比較。 -/
def constantDiamondEdgeComparison : EndpointFixedEdgeCylinder e c where
  homotopy := familyHomotopyEndpointTransport
    (endpointFixedDiamondComparison (constantDiamondAtSourceData D ha hb hd he).2.val)
    ((constantEdge_source e he).trans (mappingIdentityEdge_map x).symm)
    (congrArg SSet.yonedaEquiv.symm (constantDiamondAtSourceData D ha hb hd he).2.property.1)
  relative := by
    rw [familyHomotopyEndpointTransport_h, endpointFixedDiamondComparison_relative]
    exact congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
      ((mappingIdentityEdge_map x).trans (constantEdge_source e he).symm)

/-- 元の両全三角形と実比較円柱を指定面に保持する同じ高次比較。 -/
def constantDiamondEdgeComparisonRealization :=
  endpointFixedDiamondComparisonRealization (constantDiamondAtSourceData D ha hb hd he).2.val

/-- 指定比較面は、構成した同じ全端点固定円柱そのもの。 -/
lemma constantDiamondEdgeComparisonRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        constantDiamondEdgeComparisonRealization D ha hb hd he =
      (constantDiamondEdgeComparison D ha hb hd he).homotopy.h := by
  rw [constantDiamondEdgeComparisonRealization,
    endpointFixedDiamondComparisonRealization_comparison]
  change _ = (familyHomotopyEndpointTransport _ _ _).h
  exact (familyHomotopyEndpointTransport_h _ _ _).symm

/-- 元の第一全三角形は、同じ高次比較の指定面にそのまま保持する。 -/
lemma constantDiamondEdgeComparisonRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        constantDiamondEdgeComparisonRealization D ha hb hd he =
      SSet.yonedaEquiv.symm D.first.simplex := by
  rw [constantDiamondEdgeComparisonRealization,
    endpointFixedDiamondComparisonRealization_first_triangle,
    (constantDiamondAtSourceData D ha hb hd he).2.property.2.1]

/-- 元の第二全三角形も、同じ高次比較の指定面にそのまま保持する。 -/
lemma constantDiamondEdgeComparisonRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        constantDiamondEdgeComparisonRealization D ha hb hd he =
      SSet.yonedaEquiv.symm D.second.simplex := by
  rw [constantDiamondEdgeComparisonRealization,
    endpointFixedDiamondComparisonRealization_second_triangle,
    (constantDiamondAtSourceData D ha hb hd he).2.property.2.2]

/-- 高次比較全体も、元の区間境界を全パラメータで厳密に固定する。 -/
lemma constantDiamondEdgeComparisonRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        constantDiamondEdgeComparisonRealization D ha hb hd he =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm e.edge := by
  rw [constantDiamondEdgeComparisonRealization, endpointFixedDiamondComparisonRealization_relative]
  exact congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫ q)
    ((mappingIdentityEdge_map x).trans (constantEdge_source e he).symm)

end SerrePositivity.KST.SConstruction
