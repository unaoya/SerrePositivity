module
public import SerrePositivity.KST.SConstruction.TriangleEdgeTransportFromZero
public import SerrePositivity.KST.SConstruction.FixedBoundaryTargetEdges

/-! # 元の全三角形の上辺だけを指定円柱で移す
概要：元の全三角形を時刻零に保持し、二辺を全時刻固定したまま上辺だけを移す。
方針：元の同じ二単体を合成三角形として表示し、全境界固定円柱を相対移送へ渡す。
規約：元の全二単体・二固定辺・入力した全円柱を厳密に回収する。
使われ方：元の各段 span 三角形の比較面を実 BF 段辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の全三角形と二固定辺を保持し、指定上辺へ移す同じ全比較のデータ。 -/
structure TriangleUpperFaceTransportData {E : SSet.{u}} (t : (Δ[2] : SSet.{u}) ⟶ E)
    (g : (Δ[1] : SSet.{u}) ⟶ E) (H : Homotopy (stdSimplex.δ 0 ≫ t) g) where
  /-- 指定した新しい上辺を持つ全三角形。 -/
  val : (Δ[2] : SSet.{u}) ⟶ E
  /-- 新しい全上辺は入力した同じ全写像。 -/
  face_zero : stdSimplex.δ 0 ≫ val = g
  /-- 元の全対角辺を保持する。 -/
  face_one : stdSimplex.δ 1 ≫ val = stdSimplex.δ 1 ≫ t
  /-- 元の全下辺を保持する。 -/
  face_two : stdSimplex.δ 2 ≫ val = stdSimplex.δ 2 ≫ t
  /-- 元の全三角形から新しい全三角形へ出る同じ実比較円柱。 -/
  comparison : Homotopy t val
  /-- 動く上辺側面は入力した同じ全比較円柱。 -/
  comparison_zero : (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ comparison.h = H.h
  /-- 元の全対角辺を全比較時刻で固定する。 -/
  comparison_one : (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ 1 ≫ t
  /-- 元の全下辺も全比較時刻で固定する。 -/
  comparison_two : (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ 2 ≫ t

/-- 元の全三角形の二辺を固定し、上辺だけを元の全円柱に沿って相対移送する。 -/
def triangleUpperFaceTransportData {E : SSet.{u}} [KanComplex E]
    (t : (Δ[2] : SSet.{u}) ⟶ E) (g : (Δ[1] : SSet.{u}) ⟶ E)
    (H : Homotopy (stdSimplex.δ 0 ≫ t) g)
    (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ stdSimplex.δ 0 ≫ t) :
    TriangleUpperFaceTransportData t g H := by
  apply Classical.choice
  obtain ⟨x, y, z, a, b, c, T, hT⟩ := SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have hb : SSet.yonedaEquiv.symm b.edge = stdSimplex.δ 0 ≫ t :=
    (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 0 ≫ ·) ht)
  have hc : SSet.yonedaEquiv.symm c.edge = stdSimplex.δ 1 ≫ t :=
    (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 1 ≫ ·) ht)
  have ha : SSet.yonedaEquiv.symm a.edge = stdSimplex.δ 2 ≫ t :=
    (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 2 ≫ ·) ht)
  let K := familyHomotopyEndpointTransport H hb rfl
  have hK : K.h = H.h := familyHomotopyEndpointTransport_h _ _ _
  have hrK : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm b.edge := by
    rw [hK]
    exact hr.trans (congrArg (fun q => fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
      hb.symm)
  let C := fixedBoundaryTargetCylinder b K hrK
  let A := endpointFixedEdgeCylinderRefl a
  let B := endpointFixedEdgeCylinderRefl c
  let M := triangleEdgeTransportFromZero A C B T
  let V := triangleEdgeTransportFromZeroComparison A C B T
  let W := familyHomotopyEndpointTransport V ht.symm rfl
  have hW : W.h = V.h := familyHomotopyEndpointTransport_h _ _ _
  refine ⟨⟨SSet.yonedaEquiv.symm M.simplex, ?_, ?_, ?_, W, ?_, ?_, ?_⟩⟩
  · exact (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm M).trans
      (fixedBoundaryTargetEdgeData b K hrK).property
  · exact (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm M).trans hc
  · exact (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm M).trans ha
  · exact (congrArg ((stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ ·) hW).trans
      ((triangleEdgeTransportFromZeroComparison_face A C B T 0).trans
        ((fixedBoundaryTargetCylinder_h b K hrK).trans hK))
  · exact (congrArg ((stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ ·) hW).trans
      ((triangleEdgeTransportFromZeroComparison_face A C B T 1).trans
        (congrArg (fst (Δ[1] : SSet.{u}) Δ[1] ≫ ·) hc))
  · exact (congrArg ((stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫ ·) hW).trans
      ((triangleEdgeTransportFromZeroComparison_face A C B T 2).trans
        (congrArg (fst (Δ[1] : SSet.{u}) Δ[1] ≫ ·) ha))

end SerrePositivity.KST.SConstruction
