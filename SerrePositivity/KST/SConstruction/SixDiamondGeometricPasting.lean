module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionTripleRightTetrahedron
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondComposition
public import SerrePositivity.KST.SConstruction.TriangleRightCancellation
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellation
public import SerrePositivity.KST.SConstruction.TriangleEdgeTransportFromZero

/-! # 六対角面を全実四面体と全円柱で消去する
概要：六組の共有対角三角形と共有直接円柱から、指定二辺の全端点固定比較を構成する。
方針：六つの結合替え四面体、終辺消去、三辺移送、始辺消去を順に保持する。
規約：元の十二面と共有直接円柱を実面・全境界として保持し、類の消去で終えない。
使われ方：元の十二面 raw 複体の辺路消去を、高次 prism に沿う実構成へ置き換える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : E _⦋0⦌}
  {s t : E.Edge v₀ v₁} {leftEdge generatedEdge : E.Edge v₁ v₂}
  {r : E.Edge v₂ v₃} {p : E.Edge v₀ v₄} {l : E.Edge v₄ v₂}
  {q : E.Edge v₄ v₅} {k₁ : E.Edge v₀ v₆} {k₂ : E.Edge v₆ v₅}
  {k₃ : E.Edge v₅ v₃} {a : E.Edge v₆ v₇} {e : E.Edge v₇ v₃} {b : E.Edge v₁ v₇}

/-- 元の十二面を保持する六四面体と、両消去・全三辺移送の実データ。 -/
structure SixDiamondGeometricPasting
    (DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p q k₁ k₂) (DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃)
    (DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃) (DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p l)
    (DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a) (DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r)
    (H : EndpointFixedEdgeCylinder s t) where
  /-- 左対角と共通終辺の同じ実合成。 -/
  top : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition DL.diagonal r
  /-- 左外側面と交換第一面を同じ実四面体で結合替えする。 -/
  firstMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DL.second DI.first top.triangle
  /-- 前二射段面と交換第二面を同じ実四面体で結合替えする。 -/
  secondMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron DA.first DI.second firstMove.right
  /-- 前二射二部分面と後二射二部分面を同じ実四面体で結合替えする。 -/
  thirdMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DA.second DB.second secondMove.left
  /-- 右外側二部分面と後二射段面を同じ実四面体で結合替えする。 -/
  fourthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron DR.second DB.first thirdMove.right
  /-- 右外側段面と第一 BF 面を同じ実四面体で結合替えする。 -/
  fifthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DR.first DF.first fourthMove.left
  /-- 右直接辺と生成第四辺の同じ実合成。 -/
  bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition t generatedEdge
  /-- 第二 BF 面を同じ実四面体で結合替えする。 -/
  sixthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron bottom.triangle DF.second fifthMove.right
  /-- 共通終辺の消去は、元の両全合成面を保持する実四面体。 -/
  suffixChoice : (triangleRightCancellationChoices top.triangle sixthMove.left) _⦋0⦌
  /-- 元の左段面の全三辺を同時に移送した実三角形。 -/
  transported : SSet.Edge.CompStruct t leftEdge bottom.edge
  /-- 元の同じ左段面全体を始端に保持する実移送円柱。 -/
  transportComparison : SSet.Homotopy (SSet.yonedaEquiv.symm DL.first.simplex)
    (SSet.yonedaEquiv.symm transported.simplex)
  /-- 同じ全境界に元の共有直接円柱・固定辺・同じ終辺消去円柱を保持する。 -/
  transport_boundary : ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫ transportComparison.h =
    (triangleBoundaryHomotopy H (endpointFixedEdgeCylinderRefl leftEdge)
      (triangleRightCancellationCylinder top.triangle sixthMove.left suffixChoice)).h
  /-- 共通始辺の消去も、元の両全合成面を保持する実四面体。 -/
  prefixChoice : (triangleLeftCancellationChoices transported bottom.triangle) _⦋0⦌

variable [KanComplex E]
  (DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p q k₁ k₂) (DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃)
  (DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃) (DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p l)
  (DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a) (DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r)
  (H : EndpointFixedEdgeCylinder s t)

/-- 元の十二面と全共有直接円柱を保つ、辺路消去の実四面体・実円柱の全データ。 -/
def sixDiamondGeometricPasting : SixDiamondGeometricPasting DA DB DI DL DR DF H := by
  let top := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition DL.diagonal r
  let M₁ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleRightTetrahedron DL.second DI.first top.triangle
  let M₂ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedron DA.first DI.second M₁.right
  let M₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleRightTetrahedron DA.second DB.second M₂.left
  let M₄ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedron DR.second DB.first M₃.right
  let M₅ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleRightTetrahedron DR.first DF.first M₄.left
  let bottom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition t generatedEdge
  let M₆ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedron bottom.triangle DF.second M₅.right
  let v := (triangleRightCancellationChoices_isContractibleKan top.triangle M₆.left).nonempty.some
  let C := triangleRightCancellationCylinder top.triangle M₆.left v
  let T := triangleEdgeTransportFromZero H (endpointFixedEdgeCylinderRefl leftEdge) C DL.first
  let w := (triangleLeftCancellationChoices_isContractibleKan T bottom.triangle).nonempty.some
  exact ⟨top, M₁, M₂, M₃, M₄, M₅, bottom, M₆, v, T,
    triangleEdgeTransportFromZeroComparison H (endpointFixedEdgeCylinderRefl leftEdge) C DL.first,
    triangleEdgeTransportFromZeroComparison_boundary H
      (endpointFixedEdgeCylinderRefl leftEdge) C DL.first, w⟩

omit [KanComplex E]

/-- 六対角面の同じ実データから得られる全端点固定の指定二辺比較円柱。 -/
def SixDiamondGeometricPasting.comparison
    (D : SixDiamondGeometricPasting DA DB DI DL DR DF H) :
    EndpointFixedEdgeCylinder leftEdge generatedEdge :=
  triangleLeftCancellationCylinder D.transported D.bottom.triangle D.prefixChoice

/-- 最終比較面も、同じ始辺消去四面体の全零面そのもの。 -/
lemma SixDiamondGeometricPasting.comparison_triangle
    (D : SixDiamondGeometricPasting DA DB DI DL DR DF H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ D.comparison.homotopy.h =
      stdSimplex.δ 0 ≫ triangleLeftCancellationAt D.transported D.bottom.triangle D.prefixChoice :=
  triangleLeftCancellationCylinder_triangle _ _ _

end SerrePositivity.KST.SConstruction
