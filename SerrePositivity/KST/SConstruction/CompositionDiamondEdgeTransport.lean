module
public import SerrePositivity.KST.SConstruction.TriangleEdgeTransport
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondComposition

/-! # 共通対角辺を固定する全三角形対の辺移送
概要：四辺の端点固定円柱で二三角形を移送し、元の共通対角辺を全時刻固定する。
方針：対角辺には定数円柱を使い、二つの元の全三角形へ同じ相対移送を適用する。
規約：元の二単体を終端に保持する。独立の第四比較辺との一致は仮定しない。
使われ方：元の BF 比較三辺と生成された第四辺を持つ三入力の実三角形対。
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
  {a₀ a₁ : E.Edge x m} {b₀ b₁ : E.Edge m z}
  {c₀ c₁ : E.Edge x n} {d₀ d₁ : E.Edge n z}
  (Ha : EndpointFixedEdgeCylinder a₀ a₁) (Hb : EndpointFixedEdgeCylinder b₀ b₁)
  (Hc : EndpointFixedEdgeCylinder c₀ c₁) (Hd : EndpointFixedEdgeCylinder d₀ d₁)
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a₁ b₁ c₁ d₁)

/-- 元の共通対角辺を持ち、四辺だけを指定円柱で移した実三角形対。 -/
def compositionDiamondEdgeTransport : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a₀ b₀ c₀ d₀ where
  diagonal := D.diagonal
  first := triangleEdgeTransport Ha Hb (endpointFixedEdgeCylinderRefl D.diagonal) D.first
  second := triangleEdgeTransport Hc Hd (endpointFixedEdgeCylinderRefl D.diagonal) D.second

/-- 第一の全三角形を元の同じ全三角形へ戻す実比較円柱。 -/
def compositionDiamondEdgeTransportFirstComparison : Homotopy
    (SSet.yonedaEquiv.symm (compositionDiamondEdgeTransport Ha Hb Hc Hd D).first.simplex)
    (SSet.yonedaEquiv.symm D.first.simplex) :=
  triangleEdgeTransportComparison Ha Hb (endpointFixedEdgeCylinderRefl D.diagonal) D.first

/-- 第二の全三角形も、元の同じ全三角形へ戻す実比較円柱を持つ。 -/
def compositionDiamondEdgeTransportSecondComparison : Homotopy
    (SSet.yonedaEquiv.symm (compositionDiamondEdgeTransport Ha Hb Hc Hd D).second.simplex)
    (SSet.yonedaEquiv.symm D.second.simplex) :=
  triangleEdgeTransportComparison Hc Hd (endpointFixedEdgeCylinderRefl D.diagonal) D.second

/-- 第一の全比較でも、元の共通対角辺全体を全時刻で厳密に固定する。 -/
lemma compositionDiamondEdgeTransportFirstComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (compositionDiamondEdgeTransportFirstComparison Ha Hb Hc Hd D).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm D.diagonal.edge :=
  triangleEdgeTransportComparison_fixed_diagonal Ha Hb
    (endpointFixedEdgeCylinderRefl D.diagonal) D.first rfl

/-- 第二の全比較でも、同じ元の共通対角辺全体を全時刻で厳密に固定する。 -/
lemma compositionDiamondEdgeTransportSecondComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (compositionDiamondEdgeTransportSecondComparison Ha Hb Hc Hd D).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm D.diagonal.edge :=
  triangleEdgeTransportComparison_fixed_diagonal Hc Hd
    (endpointFixedEdgeCylinderRefl D.diagonal) D.second rfl

/-- 第一比較の各側面は、入力円柱または元の対角辺の同じ定数円柱。 -/
lemma compositionDiamondEdgeTransportFirstComparison_face (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (compositionDiamondEdgeTransportFirstComparison Ha Hb Hc Hd D).h =
      triangleBoundaryCylinderRawFaces Ha Hb (endpointFixedEdgeCylinderRefl D.diagonal) i :=
  triangleEdgeTransportComparison_face Ha Hb (endpointFixedEdgeCylinderRefl D.diagonal) D.first i

/-- 第二比較の各側面も、入力円柱または同じ対角辺の同じ定数円柱。 -/
lemma compositionDiamondEdgeTransportSecondComparison_face (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (compositionDiamondEdgeTransportSecondComparison Ha Hb Hc Hd D).h =
      triangleBoundaryCylinderRawFaces Hc Hd (endpointFixedEdgeCylinderRefl D.diagonal) i :=
  triangleEdgeTransportComparison_face Hc Hd (endpointFixedEdgeCylinderRefl D.diagonal) D.second i

end SerrePositivity.KST.SConstruction
