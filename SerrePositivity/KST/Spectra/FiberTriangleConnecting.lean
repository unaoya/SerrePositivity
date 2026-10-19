module

public import SerrePositivity.KST.Spectra.FiberTriangleReduction
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：相対三角形の三辺の積と実際の連結準同型の一致。
方針：先頭辺を相対充填で消去し、最後の二面を既存の終端ホーンでまとめる。
規約：基本群の非可換な積の順序を保持する。
使われ方：Goerss–Jardine I §8、VIII §1。cochain 次数一の境界公式。
-/

@[expose] public section
universe u v
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.FiberTriangle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 底の二単体の連結像は、三辺の指定した順序の積。 -/
theorem connecting_product {E B : SSet.{u}} {p : E ⟶ B}
    [Fibration p] [KanComplex E] [KanComplex B] {e : E _⦋0⦌}
    {s : B.PtSimplex 2 (p.app _ e)}
    {a : Fin 3 → (KanFiber p (p.app _ e)).PtSimplex 1 (fiberPoint p e)}
    (T : SphericalFiberLift p e s a) :
    connectingHom p e 0 (KanHomotopyGroup.mk s) =
      (KanHomotopyGroup.mk (a 1))⁻¹ * KanHomotopyGroup.mk (a 2) *
        KanHomotopyGroup.mk (a 0) := by
  obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse (a 0) (0 : Fin 1)
  obtain ⟨b, ⟨hb⟩⟩ := exists_left_factor ia (a 2) (0 : Fin 1)
  let T' := reduce hi hb T
  obtain ⟨ia₁, ⟨hi₁⟩⟩ := PtSimplex.MulStruct.exists_left_inverse
    (reduced a b (1 : Fin 3)) (0 : Fin 1)
  obtain ⟨c, ⟨hc⟩⟩ := PtSimplex.MulStruct.nonempty ia₁
    (reduced a b (2 : Fin 3)) (0 : Fin 1)
  have hlower : ∀ j : Fin 3, j.val < 1 → reduced a b j = .const := by
    intro j hj
    have hj' : j = 0 := Fin.ext (by omega)
    subst j
    simp [reduced]
  have hconn : connectingHom p e 0 (KanHomotopyGroup.mk s) = KanHomotopyGroup.mk c := by
    change connecting p e 1 (KanHomotopyGroup.mk s) = _
    rw [connecting_eq p e (SphericalFiberLift.terminalLift hi₁ hc T' hlower),
      SphericalFiberLift.terminalLift_boundary]
    rfl
  have hi' : KanHomotopyGroup.mk ia = (KanHomotopyGroup.mk (a 0))⁻¹ :=
    eq_inv_of_mul_eq_one_left (KanHomotopyGroup.mul_eq hi)
  have hb' : KanHomotopyGroup.mk b = KanHomotopyGroup.mk (a 2) *
      KanHomotopyGroup.mk (a 0) := by
    have h := eq_mul_inv_of_mul_eq (KanHomotopyGroup.mul_eq hb)
    simpa only [hi', inv_inv] using h
  have hi₁' : KanHomotopyGroup.mk ia₁ = (KanHomotopyGroup.mk (a 1))⁻¹ := by
    have h := eq_inv_of_mul_eq_one_left (KanHomotopyGroup.mul_eq hi₁)
    simpa only [reduced, Fin.reduceEq, ite_false] using h
  rw [hconn, ← KanHomotopyGroup.mul_eq hc]
  simp only [reduced, Fin.reduceEq, ite_false, ite_true]
  rw [hi₁', hb', mul_assoc]

/-- 可換群へ移した三辺の交代和は、底の二単体の連結像。 -/
theorem alternating_connecting {E B : SSet.{u}} {p : E ⟶ B}
    [Fibration p] [KanComplex E] [KanComplex B] {e : E _⦋0⦌}
    {s : B.PtSimplex 2 (p.app _ e)}
    {a : Fin 3 → (KanFiber p (p.app _ e)).PtSimplex 1 (fiberPoint p e)}
    (T : SphericalFiberLift p e s a) {G : Type v} [CommGroup G]
    (φ : KanHomotopyGroup (KanFiber p (p.app _ e)) 0 (fiberPoint p e) →* G) :
    (∑ j : Fin 3, (-1 : ℤ) ^ j.val • Additive.ofMul (φ (KanHomotopyGroup.mk (a j)))) =
      Additive.ofMul (φ (connectingHom p e 0 (KanHomotopyGroup.mk s))) := by
  rw [connecting_product T, φ.map_mul, φ.map_mul, φ.map_inv]
  simp only [ofMul_mul, ofMul_inv, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
    one_zsmul, Fin.val_succ, Fin.sum_univ_zero, add_zero]
  norm_num
  abel

end
end SerrePositivity.KST.Spectra.FiberTriangle
