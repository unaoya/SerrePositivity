module
public import SerrePositivity.KST.SConstruction.SixDiamondGeometricPasting
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionDiamondImages

/-! # 六つの結合替えを元の全面と共有面に沿って同時に保持する
概要：元の六対角面からの六つの結合替え四面体を、同じ全共有面で束ねる。
方針：前の四面体の出力面を次の入力面そのものとする依存データを使う。
規約：六つを独立に選んだデータに弱めず、終辺・始辺消去の完成とは区別する。
使われ方：元の全基底四面体を保持する六結合替えの同時持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
variable {E : SSet.{u}} {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : E _⦋0⦌}
  {s t : E.Edge v₀ v₁} {leftEdge generatedEdge : E.Edge v₁ v₂}
  {r : E.Edge v₂ v₃} {p₀ : E.Edge v₀ v₄} {l : E.Edge v₄ v₂}
  {q : E.Edge v₄ v₅} {k₁ : E.Edge v₀ v₆} {k₂ : E.Edge v₆ v₅}
  {k₃ : E.Edge v₅ v₃} {a : E.Edge v₆ v₇} {e : E.Edge v₇ v₃} {b : E.Edge v₁ v₇}
  {topEdge : E.Edge v₀ v₃} {bottomEdge : E.Edge v₀ v₂}

/-- 元の十二面と全共有面を保持する、連続した六つの実結合替え四面体。 -/
structure SixDiamondReassociations
    (DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p₀ q k₁ k₂) (DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃)
    (DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃) (DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p₀ l)
    (DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a) (DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r)
    (top : SSet.Edge.CompStruct DL.diagonal r topEdge)
    (bottom : SSet.Edge.CompStruct t generatedEdge bottomEdge) where
  /-- 左外側面と交換第一面の結合替え。 -/
  firstMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DL.second DI.first top
  /-- 前二射段面と交換第二面の結合替え。 -/
  secondMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron DA.first DI.second firstMove.right
  /-- 前後二射二部分面の結合替え。 -/
  thirdMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DA.second DB.second secondMove.left
  /-- 右外側二部分面と後二射段面の結合替え。 -/
  fourthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron DR.second DB.first thirdMove.right
  /-- 右外側段面と第一 BF 面の結合替え。 -/
  fifthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron DR.first DF.first fourthMove.left
  /-- 第二 BF 面と同じ右直接辺・生成辺の合成面の結合替え。 -/
  sixthMove : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron bottom DF.second fifthMove.right

/-- 元の実消去から、元の全面・全共有面を持つ同じ六結合替えを取り出す。 -/
def SixDiamondGeometricPasting.reassociations
    {DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p₀ q k₁ k₂} {DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃}
    {DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃} {DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p₀ l}
    {DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a} {DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r}
    {H : EndpointFixedEdgeCylinder s t} (D : SixDiamondGeometricPasting DA DB DI DL DR DF H) :
    SixDiamondReassociations DA DB DI DL DR DF D.top.triangle D.bottom.triangle :=
  ⟨D.firstMove, D.secondMove, D.thirdMove, D.fourthMove, D.fifthMove, D.sixthMove⟩

end SerrePositivity.KST.SConstruction
