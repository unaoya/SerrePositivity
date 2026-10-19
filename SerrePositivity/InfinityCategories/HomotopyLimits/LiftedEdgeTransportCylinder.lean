module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismTransportCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedEdgeTransportPointIso

/-!
概要：付加比較に使う実際の持ち上げ辺を、底と始点を固定する prism 円柱として保持する。
方針：元の辺を一点の prism にし、標準 prism との同じ相対比較を終点で評価する。
規約：既存の輸送同型の類と一致させる。使われ方：指定境界経路の付加辺の部分の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b)
  (v : (vertexFiber p a) _⦋0⦌) (w : (vertexFiber p b) _⦋0⦌)
  (k : E.Edge v.val w.val) (hk : (k.map p).edge = e.edge)

/-- 元の持ち上げ辺自身を、一点係数の全 prism として保持する。 -/
def liftedEdgePointPrism : (Δ[1] : SSet.{u}) ⊗ Δ[0] ⟶ E :=
  fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm k.edge

omit [LeftFibration p] in
/-- 一点 prism の始点は、元の始点 fiber の同じ点。 -/
lemma liftedEdgePointPrism_zero : prismEndpoint 0 Δ[0] ≫ liftedEdgePointPrism p v w k =
      SSet.yonedaEquiv.symm v ≫ vertexFiberι p a := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (SSet.yonedaEquiv.symm k.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = v.val
    rw [SSet.yonedaEquiv_symm_app]
    have he : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        SimplexCategory.δ (1 : Fin 2) := by decide
    rw [he]
    exact k.src_eq

omit [LeftFibration p] in
/-- 一点 prism の終点は、元の終点 fiber の同じ点。 -/
lemma liftedEdgePointPrism_one : prismEndpoint 1 Δ[0] ≫ liftedEdgePointPrism p v w k =
      SSet.yonedaEquiv.symm w ≫ vertexFiberι p b := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (SSet.yonedaEquiv.symm k.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = w.val
    rw [SSet.yonedaEquiv_symm_app]
    have he : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SimplexCategory.δ (0 : Fin 2) := by decide
    rw [he]
    exact k.tgt_eq

include hk in
omit [LeftFibration p] in
/-- 一点 prism の底は、元の指定辺そのもの。 -/
lemma liftedEdgePointPrism_projection :
    liftedEdgePointPrism p v w k ≫ p = fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm e.edge := by
    dsimp only [liftedEdgePointPrism]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun s ↦ fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm s) hk

/-- 元の辺と同じ標準輸送 prism を結ぶ、底・初期値固定の実際の比較データ。 -/
def liftedEdgeTransportCylinderData :=
  prismTransportCylinder p e (SSet.yonedaEquiv.symm v) (liftedEdgePointPrism p v w k)
    (liftedEdgePointPrism_zero p v w k) (liftedEdgePointPrism_projection p e v w k hk)

/-- 指定した元の持ち上げ辺による、実際の終点比較円柱。 -/
def liftedEdgeTransportEndpointHomotopy : SSet.Homotopy (SSet.yonedaEquiv.symm w)
    (SSet.yonedaEquiv.symm v ≫ edgeTransport p e) :=
  prismTransportEndpointHomotopy p e (SSet.yonedaEquiv.symm v) (liftedEdgePointPrism p v w k)
    (liftedEdgePointPrism_zero p v w k) (liftedEdgePointPrism_projection p e v w k hk)
    (SSet.yonedaEquiv.symm w) (liftedEdgePointPrism_one p v w k)

/-- 終点円柱は、元の一点 prism の底と初期値を保つ円柱の同じ終点制限。 -/
lemma liftedEdgeTransportEndpointHomotopy_projection :
    (liftedEdgeTransportEndpointHomotopy p e v w k hk).h ≫ vertexFiberι p b =
      (prismEndpoint 1 (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        (liftedEdgeTransportCylinderData p e v w k hk).homotopy.h :=
  prismTransportEndpointHomotopy_projection _ _ _ _ _ _ _ _

/-- 新たに保持した実際の円柱の類は、既存の持ち上げ辺の輸送同型の射そのもの。 -/
lemma liftedEdgeTransportEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (liftedEdgeTransportEndpointHomotopy p e v w k hk)) =
      (liftedEdgeTransportPointIso p e v w k hk).hom :=
  prismTransportEndpointHomotopy_hom p e (SSet.yonedaEquiv.symm v) (liftedEdgePointPrism p v w k)
    (liftedEdgePointPrism_zero p v w k) (liftedEdgePointPrism_projection p e v w k hk)
    (SSet.yonedaEquiv.symm w) (liftedEdgePointPrism_one p v w k)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
