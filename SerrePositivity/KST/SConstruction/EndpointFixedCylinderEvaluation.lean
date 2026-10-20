module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 端点固定円柱の評価表示を全円柱ごと移す
概要：辺の写像として表した円柱を、元の全辺の後合成として表示し直す。
方針：Yoneda 表示の自然性で両端だけを移し、元の全円柱と全境界固定式を保持する。
規約：新しい円柱を選ばず、表示の等号と境界固定は一般の辺について証明する。
使われ方：零段固定の raw 比較族を、隣接段の構造作用の入力へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E B : SSet.{u}} {x y : E _⦋0⦌} (a b : E.Edge x y) (p : E ⟶ B)
  (H : EndpointFixedEdgeCylinder (a.map p) (b.map p))

/-- 同じ全辺の後合成を両端とし、元の全円柱を保持する表示。 -/
def endpointFixedCylinderEvaluation : SSet.Homotopy
    (SSet.yonedaEquiv.symm a.edge ≫ p) (SSet.yonedaEquiv.symm b.edge ≫ p) :=
  familyHomotopyEndpointTransport H.homotopy
    (SSet.yonedaEquiv_symm_comp a.edge p) (SSet.yonedaEquiv_symm_comp b.edge p).symm

/-- 表示の移送で全円柱の写像は変わらない。 -/
lemma endpointFixedCylinderEvaluation_h :
    (endpointFixedCylinderEvaluation a b p H).h = H.homotopy.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 表示を移しても、元の入力区間の全境界を全比較時刻で厳密に固定する。 -/
lemma endpointFixedCylinderEvaluation_relative :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (endpointFixedCylinderEvaluation a b p H).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm a.edge ≫ p := by
  rw [endpointFixedCylinderEvaluation_h, H.relative]
  simp only [SSet.yonedaEquiv_symm_comp, SSet.Edge.map_edge]

end SerrePositivity.KST.SConstruction
