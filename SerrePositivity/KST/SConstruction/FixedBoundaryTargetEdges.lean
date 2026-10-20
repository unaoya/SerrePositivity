module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders

/-! # 全境界固定円柱の終端写像を同じ端点の実辺として回収
概要：元の辺から出る全境界固定円柱の終端を、同じ二頂点を持つ全実辺にする。
方針：全境界固定式を終端へ制限して元の二頂点を回収し、同じ全一単体を保持する。
規約：新しい辺を充填せず、入力した終端写像と全円柱を厳密に保存する。
使われ方：元の全 span 三角形の比較面を、実 BF 段辺へ相対移送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y)
  {g : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy (SSet.yonedaEquiv.symm a.edge) g)
  (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge)

include H hr in
/-- 全境界固定円柱の終端は、元の辺と同じ全区間境界を持つ。 -/
lemma fixedBoundaryTarget_boundary :
    (SSet.boundary 1).ι ≫ g = (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge := by
  calc
    _ = (SSet.boundary 1).ι ≫ SSet.ι₁ ≫ H.h := by rw [H.h₁]
    _ = SSet.ι₁ ≫ ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
      rw [SSet.ι₁_comp_assoc]
    _ = _ := by rw [hr, SSet.ι₁_fst_assoc]

/-- 元の終端写像全体を保持し、元の同じ両端を持つ実辺を回収する。 -/
def fixedBoundaryTargetEdgeData : {b : E.Edge x y // SSet.yonedaEquiv.symm b.edge = g} := by
  have hb (i : Fin 2) : stdSimplex.δ i ≫ g = stdSimplex.δ i ≫
      SSet.yonedaEquiv.symm a.edge := by
    rw [← SSet.boundary.ι_ι i, Category.assoc, fixedBoundaryTarget_boundary a H hr,
      SSet.boundary.ι_ι_assoc, SSet.boundary.ι_ι]
  let b : E.Edge x y := SSet.Edge.mk (SSet.yonedaEquiv g)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, hb 1,
          SSet.Edge.δ_one_yonedaEquiv_symm, Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, hb 0,
          SSet.Edge.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply])
  exact ⟨b, Equiv.symm_apply_apply _ _⟩

/-- 元の終端写像を持つ同じ全辺への、元の同じ全端点固定円柱。 -/
def fixedBoundaryTargetCylinder :
    EndpointFixedEdgeCylinder a (fixedBoundaryTargetEdgeData a H hr).val where
  homotopy := familyHomotopyEndpointTransport H rfl
    (fixedBoundaryTargetEdgeData a H hr).property.symm
  relative := by rw [familyHomotopyEndpointTransport_h]; exact hr

/-- 終端辺の表示を回収しても、入力した元の全円柱を厳密に保持する。 -/
lemma fixedBoundaryTargetCylinder_h : (fixedBoundaryTargetCylinder a H hr).homotopy.h = H.h :=
  familyHomotopyEndpointTransport_h _ _ _

end SerrePositivity.KST.SConstruction
