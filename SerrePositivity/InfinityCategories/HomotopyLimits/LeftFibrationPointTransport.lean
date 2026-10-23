module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
概要：元の持ち上げ辺の終点と、元の選択した輸送点を比較する。
方針：係数が標準一点の元の辺 prism を、同じ始点を持つ標準輸送 prism と比較する。
規約：指定した辺の射影は元の底の辺と厳密に一致するものを使う。
使われ方：二方向の Yoneda 恒等点輸送を、同じ pointed 終点へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の持ち上げ辺の終点の定値族は、同じ始点の標準輸送の族と関手同型。 -/
def leftFibrationEdge_pointTransportIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (v : (vertexFiber p a) _⦋0⦌) (w : (vertexFiber p b) _⦋0⦌)
    (l : SSet.Edge v.val w.val) (hl : p.app (Opposite.op ⦋1⦌) l.edge = e.edge) :
    FunctorIso (SSet.const w : (Δ[0] : SSet.{u}) ⟶ vertexFiber p b)
      ((SSet.const v : (Δ[0] : SSet.{u}) ⟶ vertexFiber p a) ≫ edgeTransport p e) := by
  let H := fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ SSet.yonedaEquiv.symm l.edge
  have h₀ : prismEndpoint 0 (Δ[0] : SSet.{u}) ≫ H =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ vertexFiber p a) ≫ vertexFiberι p a := by
    rw [SSet.const_comp]
    exact (prismEdgeFamily_zero l.edge).trans (congrArg SSet.const l.src_eq)
  have h₁ : prismEndpoint 1 (Δ[0] : SSet.{u}) ≫ H =
      (SSet.const w : (Δ[0] : SSet.{u}) ⟶ vertexFiber p b) ≫ vertexFiberι p b := by
    rw [SSet.const_comp]
    exact (prismEdgeFamily_one l.edge).trans (congrArg SSet.const l.tgt_eq)
  have hp : H ≫ p = fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
      SSet.yonedaEquiv.symm e.edge := by
    dsimp only [H]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp, hl]
  exact leftFibrationPrism_transportIso p e (SSet.const v) (SSet.const w) H h₀ h₁ hp

/-- 元の辺の終点は、元の同じ始点を標準輸送した点と fiber 内で同型。 -/
def leftFibrationEdge_pointVertexIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (v : (vertexFiber p a) _⦋0⦌) (w : (vertexFiber p b) _⦋0⦌)
    (l : SSet.Edge v.val w.val) (hl : p.app (Opposite.op ⦋1⦌) l.edge = e.edge) :
    VertexIso w ((edgeTransport p e).app (Opposite.op ⦋0⦌) v) := by
  have : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  have h := (leftFibrationEdge_pointTransportIso p e v w l hl).app
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  change VertexIso (PinchedHom.constant w 0)
    ((edgeTransport p e).app (Opposite.op ⦋0⦌) (PinchedHom.constant v 0)) at h
  simpa only [PinchedHom.constant_zero] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
