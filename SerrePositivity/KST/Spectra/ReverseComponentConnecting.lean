module

public import SerrePositivity.KST.Spectra.ReverseBoundaryEdge
public import SerrePositivity.KST.Spectra.PointedZeroConnecting
public import SerrePositivity.KST.Spectra.LoopBoundaryRepresentatives
public import SerrePositivity.KST.Spectra.HomotopyComponents

/-!
概要：基点から fiber の頂点への辺は、底の逆向きの loop の成分接続写像を計算する。
方針：逆辺の相対充填で BoundaryLift を作り、標準接続写像の代表公式を使う。
規約：辺自体を反転する単体的射は仮定しない。
使われ方：Goerss–Jardine I §8、VIII §1。path 延長の終点を実際の成分微分へ移す。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全空間で基点から出る辺の終点の成分は、底の逆 loop の接続写像の値。
方針：底の逆元の三角形を持ち上げ、fiber の指定頂点を保つ逆の相対充填を使う。
規約：指定した幾何的な辺から接続写像を計算する。
使われ方：Goerss–Jardine VIII §1。成分微分の幾何的代表との同定。 -/
theorem pointedConnectingZero_inverse_edge {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) [Fibration p.right] [KanComplex B.right]
    (s : B.right.PtSimplex 1 (p.right.app _ E.basepoint))
    (a : (pointedFiber p).right.PtSimplex 0 (pointedFiber p).basepoint)
    (T : (Δ[1] : SSet.{u}) ⟶ E.right)
    (hT : T ≫ p.right = s.map)
    (h₀ : stdSimplex.δ (0 : Fin 2) ≫ T = a.map ≫ (pointedFiberι p).right)
    (h₁ : stdSimplex.δ (1 : Fin 2) ≫ T = SSet.const E.basepoint) :
    pointedConnectingZero p
        ((KanHomotopyGroup.equivOfIso 0 (Iso.refl B.right)
          (OmegaSpectrum.pointedMap_basepoint p) (KanHomotopyGroup.mk s))⁻¹) =
      KanHomotopy.mk 0 a := by
  let af := SimplexBasepoint.rebase (PointedSimplicialSet.basepoint_ofVertex _ _) a
  obtain ⟨t, ⟨m⟩⟩ := PtSimplex.MulStruct.exists_left_inverse s (0 : Fin 1)
  obtain ⟨R, hR⟩ := exists_reverse_boundary_edge p.right E.basepoint af T hT h₀ h₁ m
  have ht : KanHomotopyGroup.mk t = (KanHomotopyGroup.mk s)⁻¹ :=
    eq_inv_of_mul_eq_one_left (KanHomotopyGroup.mul_eq m)
  have hr : R.pointedBoundary = a := by
    ext : 1
    change R.boundary.map = af.map
    rw [hR]
  rw [← map_inv, ← ht, pointedConnectingZero_boundaryLift p R, hr]

end
end SerrePositivity.KST.Spectra
