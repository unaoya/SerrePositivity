module
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Fin.Rev

/-!
概要：単体の頂点順序反転に伴う交代境界の符号を計算する。
方針：Fin.rev で有限和を添字替えし、反転した面番号の偶奇を negOnePow で照合する。
規約：n+1 次元の境界で全体の係数は (-1)^(n+1)。
使われ方：HA 1.2.4、G10 の反対 under 重みと over 重みの線形化比較。
-/
@[expose] public section
namespace SerrePositivity.HomologicalAlgebra

/-- n+1 次元の面番号を反転したときの符号。 -/
theorem alternating_rev_sign (n : ℕ) (i : Fin (n+2)) :
    (-1 : ℤ) ^ i.rev.val = (-1 : ℤ) ^ (n+1) * (-1 : ℤ) ^ i.val := by
  have hi : (i.rev.val : ℤ) + (i.val : ℤ) = (n+1 : ℕ) := by
    simp only [Fin.val_rev]
    omega
  rw [← Int.coe_negOnePow_natCast, ← Int.coe_negOnePow_natCast,
    ← Int.coe_negOnePow_natCast, ← Units.val_mul, ← Int.negOnePow_add]
  have he : ((n+1 : ℕ) : ℤ) + (i.val : ℤ) = (i.rev.val : ℤ) + 2 * (i.val : ℤ) := by omega
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 頂点順序の反転は交代和を全体の符号 (-1)^(n+1) 倍にする。 -/
theorem alternating_sum_rev {M : Type*} [AddCommGroup M] (n : ℕ) (f : Fin (n+2) → M) :
    (∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • f i.rev) =
      (-1 : ℤ) ^ (n+1) • ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • f i := by
  calc
    _ = ∑ i : Fin (n+2), (-1 : ℤ) ^ i.rev.val • f i := by
      simpa only [Fin.revPerm_apply, Fin.rev_rev] using
        (Equiv.sum_comp Fin.revPerm (fun i : Fin (n+2) => (-1 : ℤ) ^ i.val • f i.rev)).symm
    _ = _ := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [alternating_rev_sign, mul_smul]

end SerrePositivity.HomologicalAlgebra
