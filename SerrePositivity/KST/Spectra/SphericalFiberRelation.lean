module

public import SerrePositivity.KST.Spectra.SphericalFiberNormalization
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：fiber に入る球面的境界の交代和を連結射で計算する。
方針：射影先を固定する簡約を反復し、最後の二面を連結射へまとめる。
規約：面の次数は二以上。連結射は最後の面を取るので符号は (-1)^(n+3)。
使われ方：Goerss–Jardine I §8、VIII §1。loop と連結射の向きの比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphericalFiberLift

noncomputable section
open SphericalBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} {p : E ⟶ B} [Fibration p] [KanComplex E] [KanComplex B]
  {e : E _⦋0⦌} {n : ℕ} {s : B.PtSimplex (n + 3) (p.app _ e)}
  {a : Fin (n + 4) → (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)}

/-- 概要：最後の二面の交代和は、規約の符号を掛けた連結射に等しい。
方針：二面の差を終端ホーンから BoundaryLift とし、積を加法に移す。
規約：最初の n+2 面は定数。底の単体を変更しない。
使われ方：Goerss–Jardine I §8。相対交代境界関係の終端。 -/
theorem alternatingClass_connecting_last (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < n + 2 → a j = .const) :
    alternatingClass a = (-1 : ℤ) ^ (n + 3) •
      Additive.ofMul (connectingHom p e (n + 1) (KanHomotopyGroup.mk s)) := by
  let i := Fin.last (n + 1)
  obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse
    (a (Fin.last (n + 2)).castSucc) i
  obtain ⟨c, ⟨hc⟩⟩ := PtSimplex.MulStruct.nonempty ia (a (Fin.last (n + 2)).succ) i
  have hconn : connectingHom p e (n + 1) (KanHomotopyGroup.mk s) =
      KanHomotopyGroup.mk c := by
    change connecting p e (n + 2) (KanHomotopyGroup.mk s) = _
    rw [connecting_eq p e (terminalLift hi hc T hlower), terminalLift_boundary]
    rfl
  have hinv := KanHomotopyGroup.mul_eq_at hi
  have hmul := KanHomotopyGroup.mul_eq_at hc
  have hadd : Additive.ofMul (KanHomotopyGroup.mk c) =
      additiveClass (a (Fin.last (n + 2)).succ) -
        additiveClass (a (Fin.last (n + 2)).castSucc) := by
    have he : KanHomotopyGroup.mk c =
        KanHomotopyGroup.mk (a (Fin.last (n + 2)).succ) *
          (KanHomotopyGroup.mk (a (Fin.last (n + 2)).castSucc))⁻¹ := by
      have hinv' : KanHomotopyGroup.mk ia =
          (KanHomotopyGroup.mk (a (Fin.last (n + 2)).castSucc))⁻¹ :=
        eq_inv_of_mul_eq_one_left hinv
      rw [← hmul, hinv', mul_comm]
    exact congrArg Additive.ofMul he
  unfold alternatingClass
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.castSucc.castSucc.val •
      additiveClass (a j.castSucc.castSucc)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hlower _ j.isLt, additiveClass_const, smul_zero]
  rw [hz, zero_add, hconn, hadd]
  change (-1 : ℤ) ^ (n + 2) • additiveClass (a (Fin.last (n + 2)).castSucc) +
      (-1 : ℤ) ^ (n + 3) • additiveClass (a (Fin.last (n + 2)).succ) = _
  rw [smul_sub, show (-1 : ℤ) ^ (n + 3) = -((-1 : ℤ) ^ (n + 2)) by
    rw [pow_succ, mul_neg_one], neg_smul, neg_smul]
  rw [sub_neg_eq_add]
  exact add_comm _ _

/-- 概要：既に定数である先頭部分から、交代和と連結射の比較を進める。
方針：相対ホーンによる面の消去を反復し、交代和と底の単体を保つ。
規約：q + fuel = n+2。連結射の符号は面の最後の添字。
使われ方：Goerss–Jardine I §8。一般の相対球面的境界の計算。 -/
theorem alternatingClass_connecting_of_lower (fuel q : ℕ) (hq : q + fuel = n + 2)
    (T : SphericalFiberLift p e s a) (hlower : ∀ j, j.val < q → a j = .const) :
    alternatingClass a = (-1 : ℤ) ^ (n + 3) •
      Additive.ofMul (connectingHom p e (n + 1) (KanHomotopyGroup.mk s)) := by
  induction fuel generalizing q a with
  | zero =>
    exact alternatingClass_connecting_last T (fun j hj ↦ hlower j (by omega))
  | succ fuel ih =>
    let i : Fin (n + 2) := ⟨q, by omega⟩
    obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse (a i.castSucc.castSucc) i
    obtain ⟨b, ⟨hb⟩⟩ := exists_left_factor ia (a i.succ.succ) i
    have hl : ∀ j, j.val < i.val → a j = .const := hlower
    rw [← alternatingClass_reduce hi hb hl]
    apply ih (q + 1) (by omega) (reduce hi hb T hl)
    intro j hj
    exact ite_eq_left (show j.val ≤ i.val from by dsimp [i]; omega)

/-- 概要：fiber の球面的な面の交代和は、符号を掛けた底の連結射。
方針：相対簡約を空の先頭部分から開始し、最後の二面を正規化する。
規約：底の単体と面の実際の次数はそれぞれ n+3 と n+2。
使われ方：Goerss–Jardine I §8、VIII §1。幾何的微分の符号の実計算。 -/
theorem alternatingClass_connecting (T : SphericalFiberLift p e s a) :
    alternatingClass a = (-1 : ℤ) ^ (n + 3) •
      Additive.ofMul (connectingHom p e (n + 1) (KanHomotopyGroup.mk s)) :=
  alternatingClass_connecting_of_lower (n + 2) 0 (Nat.zero_add _) T
    (fun j hj ↦ (Nat.not_lt_zero j.val hj).elim)

end
end SerrePositivity.KST.Spectra.SphericalFiberLift
