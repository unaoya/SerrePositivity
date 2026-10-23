module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgePiZero

/-!
概要：left fibration の実際の持ち上げ辺の終点を、指定した底の辺の輸送像と同型で比較する。
方針：持ち上げ辺を一点の prism として読み、底の辺を保つ prism の比較へ渡す。
規約：元の持ち上げ辺と底の辺を保持。使われ方：付加比較辺から境界の指定経路を作る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 実際の辺が指定した底の辺を被覆すれば、その終点は同じ辺に沿う輸送像と指定同型で結ばれる。 -/
def liftedEdgeTransportPointIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b)
    (v : (vertexFiber p a) _⦋0⦌) (w : (vertexFiber p b) _⦋0⦌)
    (k : E.Edge v.val w.val) (hk : (k.map p).edge = e.edge) :
    FunctorIso (SSet.yonedaEquiv.symm w)
      (SSet.yonedaEquiv.symm v ≫ edgeTransport p e) := by
  let H : (Δ[1] : SSet.{u}) ⊗ Δ[0] ⟶ E :=
    fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm k.edge
  have h₀ : prismEndpoint 0 Δ[0] ≫ H =
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
  have h₁ : prismEndpoint 1 Δ[0] ≫ H =
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
  have hH : H ≫ p = fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm e.edge := by
    dsimp only [H]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun s ↦ fst Δ[1] Δ[0] ≫ SSet.yonedaEquiv.symm s) hk
  exact leftFibrationPrism_transportIso p e (SSet.yonedaEquiv.symm v)
    (SSet.yonedaEquiv.symm w) H h₀ h₁ hH

end
end SerrePositivity.InfinityCategories.HomotopyLimits
