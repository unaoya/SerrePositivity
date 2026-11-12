module
public import SerrePositivity.KST.SConstruction.CompositionDiamondEdgeTransport

/-! # 第一全三角形を保ち第四辺だけを相対移送
概要：同じ共通対角辺への二三角形のうち、第二の下辺だけを指定円柱で移す。
方針：第二三角形の上辺と対角辺に定数円柱を使い、第一全三角形はそのまま保存する。
規約：元の全三角形への実比較と各側面を保持し、元の辺の等号を同じデータに保存する。
使われ方：持ち上げた第四辺 raw 比較から指定 BF 四辺の実三角形対を得る。
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
  {a : E.Edge x m} {b : E.Edge m z} {c₀ c₁ : E.Edge x n} {d : E.Edge n z}
  (H : EndpointFixedEdgeCylinder c₀ c₁) (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c₁ d)

/-- 第一全三角形と共通対角辺を同じデータに保持し、第二下面だけを相対移送する。 -/
def compositionDiamondFourthEdgeTransportData :
    {T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c₀ d //
      T.first.simplex = D.first.simplex ∧ T.diagonal = D.diagonal} :=
  ⟨⟨D.diagonal, D.first, triangleEdgeTransport H (endpointFixedEdgeCylinderRefl d)
    (endpointFixedEdgeCylinderRefl D.diagonal) D.second⟩, rfl, rfl⟩

/-- 第四辺だけを指定円柱で移した実三角形対。 -/
def compositionDiamondFourthEdgeTransport := (compositionDiamondFourthEdgeTransportData H D).val

/-- 第一全三角形は元の同じ全二単体を厳密に保持する。 -/
lemma compositionDiamondFourthEdgeTransport_first :
    (compositionDiamondFourthEdgeTransport H D).first.simplex = D.first.simplex :=
  (compositionDiamondFourthEdgeTransportData H D).property.1

/-- 共通対角辺も元の同じ全辺を厳密に保持する。 -/
lemma compositionDiamondFourthEdgeTransport_diagonal :
    (compositionDiamondFourthEdgeTransport H D).diagonal = D.diagonal :=
  (compositionDiamondFourthEdgeTransportData H D).property.2

/-- 第二全三角形を元の同じ全三角形へ戻す、指定第四辺円柱を持つ全比較。 -/
def compositionDiamondFourthEdgeTransportComparison : Homotopy
    (SSet.yonedaEquiv.symm (compositionDiamondFourthEdgeTransport H D).second.simplex)
    (SSet.yonedaEquiv.symm D.second.simplex) :=
  triangleEdgeTransportComparison H (endpointFixedEdgeCylinderRefl d)
    (endpointFixedEdgeCylinderRefl D.diagonal) D.second

/-- 全比較の各面は、指定第四辺円柱または元の上辺・対角辺の同じ定数円柱。 -/
lemma compositionDiamondFourthEdgeTransportComparison_face (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (compositionDiamondFourthEdgeTransportComparison H D).h =
      triangleBoundaryCylinderRawFaces H (endpointFixedEdgeCylinderRefl d)
        (endpointFixedEdgeCylinderRefl D.diagonal) i :=
  triangleEdgeTransportComparison_face _ _ _ _ i

end SerrePositivity.KST.SConstruction
