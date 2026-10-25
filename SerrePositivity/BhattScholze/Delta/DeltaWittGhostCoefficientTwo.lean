module

public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostLowCoefficients

/-! # 第2Witt係数とδ二乗の三角形比較

p乗算単射を使い、下位座標から決まる補正を分離する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 第2Witt係数はδ²(a)と、a,δ(a)だけのp²可除性による補正の和。 -/
theorem deltaWittGhostVector_coeff_two_exists_correction (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    ∃ b : A, (deltaWittGhostVector D a).coeff 2 = D.delta (D.delta a) + b ∧
      (D.frobeniusLift a) ^ p - a ^ (p * p) = (p : A) ^ 2 * b := by
  have hd : (p : A) ^ 2 ∣ (D.frobeniusLift a) ^ p - a ^ (p * p) := by
    simpa only [pow_one, ← pow_mul] using D.frobeniusLift_pow_congruence a 1
  obtain ⟨b, hb⟩ := hd
  refine ⟨b, ?_, hb⟩
  have hc := deltaWittGhostCoefficients_ghost D a 2
  have hcoeff (i : ℕ) : deltaWittGhostCoefficients D a i = (deltaWittGhostVector D a).coeff i := rfl
  simp only [hcoeff, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, pow_zero, pow_one, one_mul, deltaWittGhostVector_coeff_zero,
    deltaWittGhostVector_coeff_one D hp] at hc
  have hf : D.frobeniusLift^[2] a = (D.frobeniusLift a) ^ p +
      (p : A) * (D.delta a) ^ p + (p : A) ^ 2 * D.delta (D.delta a) := by
    change D.frobeniusLift (D.frobeniusLift a) = _
    calc
      _ = (D.frobeniusLift a) ^ p + (p : A) * D.frobeniusLift (D.delta a) := by
        conv_lhs => rw [D.frobeniusLift_apply a]
        rw [map_add, map_pow, map_mul, map_natCast]
      _ = _ := by rw [D.frobeniusLift_apply (D.delta a)]; ring
  have hc' : D.frobeniusLift^[2] a = a ^ (p * p) +
      (p : A) * (D.delta a) ^ p + (p : A) ^ 2 * (deltaWittGhostVector D a).coeff 2 := by
    simpa only [pow_two] using hc
  apply hp
  apply hp
  linear_combination -hc' + hf + hb

/-- 下位座標から補正bを指定すれば、第2Witt係数はδ²(a)+bとなる。 -/
theorem deltaWittGhostVector_coeff_two_of_correction (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a b : A)
    (hb : (D.frobeniusLift a) ^ p - a ^ (p * p) = (p : A) ^ 2 * b) :
    (deltaWittGhostVector D a).coeff 2 = D.delta (D.delta a) + b := by
  obtain ⟨c, hcoef, hc⟩ := deltaWittGhostVector_coeff_two_exists_correction D hp a
  have hcb : c = b := by
    apply hp
    apply hp
    simpa only [pow_two, mul_assoc] using hc.symm.trans hb
  rw [hcb] at hcoef
  exact hcoef

end SerrePositivity.BhattScholze
