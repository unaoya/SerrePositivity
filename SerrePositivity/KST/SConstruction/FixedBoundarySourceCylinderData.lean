module
public import SerrePositivity.KST.SConstruction.FixedBoundaryTargetEdges

/-! # 元の境界固定円柱を指定始辺から出る実円柱として回収
概要：始端の全辺の表示を合わせ、同じ両端を持つ終辺と同じ全円柱を保持する。
方針：元の始辺の全区間の等号だけを移し、既存の終辺回収を使う。
規約：元の全円柱・終端全辺を厳密に保持し、代表を選び直さない。
使われ方：前後二射の全正規化円柱を、型の揃った六 diamond の三辺移送へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 指定始辺からの同じ全円柱と、元の終端全辺を保持するデータ。 -/
structure FixedBoundarySourceCylinderData {E : SSet.{u}} {x y : E _⦋0⦌}
    (a : E.Edge x y) {f g : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g) where
  /-- 元の終端全辺を持つ、同じ二頂点間の実辺。 -/
  target : E.Edge x y
  /-- 元の終端全辺を厳密に保持する。 -/
  target_map : SSet.yonedaEquiv.symm target.edge = g
  /-- 指定始辺と同じ終辺を結ぶ全端点固定円柱。 -/
  cylinder : EndpointFixedEdgeCylinder a target
  /-- 元の全円柱は表示の移送でも変わらない。 -/
  cylinder_h : cylinder.homotopy.h = H.h

/-- 元の始端全辺の表示を合わせ、同じ全端点固定円柱を回収する。 -/
def fixedBoundarySourceCylinderData {E : SSet.{u}} {x y : E _⦋0⦌}
    (a : E.Edge x y) {f g : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g)
    (ha : SSet.yonedaEquiv.symm a.edge = f)
    (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ f) :
    FixedBoundarySourceCylinderData a H := by
  let K := familyHomotopyEndpointTransport H ha rfl
  have hK : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge := by
    rw [familyHomotopyEndpointTransport_h, hr, ha]
  let D := fixedBoundaryTargetEdgeData a K hK
  let C := fixedBoundaryTargetCylinder a K hK
  exact ⟨D.val, D.property, C,
    (fixedBoundaryTargetCylinder_h a K hK).trans (familyHomotopyEndpointTransport_h _ _ _)⟩

end SerrePositivity.KST.SConstruction
