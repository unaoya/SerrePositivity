module
public import SerrePositivity.KST.SConstruction.EndpointFixedCylinderProjection
public import SerrePositivity.KST.SConstruction.PrescribedRawHomotopyLift

/-! # 指定した全 raw 辺円柱を端点固定で持ち上げる
概要：全単射の RLP を持つ射に沿い、元の二辺と全境界を固定して全比較円柱を持ち上げる。
方針：二辺の共通境界の定数円柱を先に指定し、元の全 raw 円柱に相対持ち上げを適用する。
規約：全 raw 円柱を射影として厳密に保存する。raw 比較の存在は仮定から隠さない。
使われ方：生成第四辺の BF 比較を、同じ実 raw 比較から構成する接続。
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
variable {E B : SSet.{u}} {x y : E _⦋0⦌} (a b : E.Edge x y)
  (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p)

/-- 共通境界を全時刻固定し、元の全 raw 円柱を厳密に回収する実持ち上げ。 -/
def endpointFixedCylinderLiftData (H : EndpointFixedEdgeCylinder (a.map p) (b.map p)) :
    {K : EndpointFixedEdgeCylinder a b // K.homotopy.h ≫ p = H.homotopy.h} := by
  let A : SSet.Homotopy
      ((SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge)
      ((SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm b.edge) :=
    familyHomotopyEndpointTransport
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge)) rfl
      (parallelEdge_boundary_eq a b)
  have hA : A.h = fst (SSet.boundary 1).toSSet Δ[1] ≫
      (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge :=
    familyHomotopyEndpointTransport_h _ _ _
  let R : SSet.Homotopy (SSet.yonedaEquiv.symm a.edge ≫ p)
      (SSet.yonedaEquiv.symm b.edge ≫ p) :=
    familyHomotopyEndpointTransport H.homotopy
      (SSet.yonedaEquiv_symm_comp a.edge p) (SSet.yonedaEquiv_symm_comp b.edge p).symm
  have hR : R.h = H.homotopy.h := familyHomotopyEndpointTransport_h _ _ _
  have h : A.h ≫ p = ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ R.h := by
    rw [hA, hR, H.relative, Category.assoc, Category.assoc,
      SSet.yonedaEquiv_symm_comp]
    rfl
  let D := prescribedRawHomotopyLiftData p hp (SSet.boundary 1).ι
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) R A h
  exact ⟨⟨D.val, D.property.2.trans hA⟩, D.property.1.trans hR⟩

include hp in
/-- 全端点固定比較の存在は、元の全 raw 射影で必要十分に判定できる。 -/
lemma endpointFixedCylinder_nonempty_iff :
    Nonempty (EndpointFixedEdgeCylinder a b) ↔
      Nonempty (EndpointFixedEdgeCylinder (a.map p) (b.map p)) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.postcomp p⟩
  · rintro ⟨H⟩
    exact ⟨(endpointFixedCylinderLiftData a b p hp H).val⟩

end SerrePositivity.KST.SConstruction
