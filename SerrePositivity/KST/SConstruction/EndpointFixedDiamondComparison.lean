module
public import SerrePositivity.KST.SConstruction.EndpointFixedTriangleHomotopy
public import SerrePositivity.KST.SConstruction.FixedBoundaryCospanComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondComposition

/-! # 共通辺への元の二実三角形から両端固定の直接比較円柱
概要：元の二辺を共通辺へ結ぶ同じ実三角形から、二辺間の両端固定実比較を得る。
方針：元の二正方形を全境界を固定する Kan 写像空間の二脚として貼り、全三面を回収する。
規約：元の全円柱・全三角形を保持し、境界で余分な loop を許さない。
使われ方：元の BF 比較辺と保存した合成面の復号辺を直接の実円柱で接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] {x y : E _⦋0⦌} {a c : E.Edge x y}
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a (SSet.Edge.id y) c (SSet.Edge.id y))

/-- 元の共通辺への全二円柱を保持する、元の二辺間の全境界固定比較データ。 -/
def endpointFixedDiamondComparisonData :
    FixedBoundaryCospanData (SSet.boundary 1).ι
      ((SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge)
      (endpointFixedTriangleHomotopy D.first) (endpointFixedTriangleHomotopy D.second) := by
  let H := endpointFixedTriangleHomotopy D.first
  let K := endpointFixedTriangleHomotopy D.second
  have hK : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm a.edge := by
    rw [endpointFixedTriangleHomotopy_relative, parallelEdge_boundary_eq c a]
  exact fixedBoundaryCospanData (SSet.boundary 1).ι
    ((SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge) rfl
    (parallelEdge_boundary_eq c a) (parallelEdge_boundary_eq D.diagonal a)
    H K (endpointFixedTriangleHomotopy_relative D.first) hK

/-- 元の二辺全体を両端に持つ、全端点固定の実比較円柱。 -/
def endpointFixedDiamondComparison :
    SSet.Homotopy (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm c.edge) :=
  (endpointFixedDiamondComparisonData D).homotopy

/-- 元の区間境界全体は、全比較時刻で厳密に固定される。 -/
lemma endpointFixedDiamondComparison_relative :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (endpointFixedDiamondComparison D).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm a.edge :=
  (endpointFixedDiamondComparisonData D).relative

/-- 元の二つの全正方形と直接比較円柱を三面に持つ、同じ実パラメータ付き二単体。 -/
def endpointFixedDiamondComparisonRealization :=
  familyCompStructRealization (endpointFixedDiamondComparisonData D).triangle

/-- 元の両円柱を持つ高次比較全体も、全パラメータで元の区間境界を固定する。 -/
lemma endpointFixedDiamondComparisonRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫ endpointFixedDiamondComparisonRealization D =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm a.edge :=
  (endpointFixedDiamondComparisonData D).triangle_relative

/-- 比較面は構成した直接比較円柱全体。 -/
lemma endpointFixedDiamondComparisonRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫ endpointFixedDiamondComparisonRealization D =
      (endpointFixedDiamondComparison D).h :=
  familyCompStructRealization_first _

/-- 第一の元の正方形全体を、同じ比較の合成面として回収する。 -/
lemma endpointFixedDiamondComparisonRealization_first :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ endpointFixedDiamondComparisonRealization D =
      (endpointFixedTriangleHomotopy D.first).h :=
  familyCompStructRealization_direct _

/-- 第二の元の正方形全体を、同じ比較の第二面として回収する。 -/
lemma endpointFixedDiamondComparisonRealization_second :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫ endpointFixedDiamondComparisonRealization D =
      (endpointFixedTriangleHomotopy D.second).h :=
  familyCompStructRealization_second _

/-- 第一の元の実三角形全体も、同じ高次比較の中の指定面として厳密に保持する。 -/
lemma endpointFixedDiamondComparisonRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        endpointFixedDiamondComparisonRealization D = SSet.yonedaEquiv.symm D.first.simplex := by
  rw [endpointFixedDiamondComparisonRealization_first]
  exact endpointFixedTriangleHomotopy_triangle D.first

/-- 第二の元の実三角形全体も、同じ高次比較の中の指定面として厳密に保持する。 -/
lemma endpointFixedDiamondComparisonRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        endpointFixedDiamondComparisonRealization D = SSet.yonedaEquiv.symm D.second.simplex := by
  rw [endpointFixedDiamondComparisonRealization_second]
  exact endpointFixedTriangleHomotopy_triangle D.second

end SerrePositivity.KST.SConstruction
