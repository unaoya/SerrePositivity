module

public import SerrePositivity.FieldTheory.PAdjoin
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Data.Nat.Find

/-! # 純非分離拡大から次数pの段階を取り出す

底体の外の元について、底体へ入る最小のFrobenius冪を選ぶ。
その一つ前の冪が非自明なp乗根となり、添加後の残りの拡大次数は厳密に減る。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP L p]

/-- 純非分離拡大の底体の外の元から、底体の外のp乗根を取り出す。
拡大の有限性は不要。 -/
theorem exists_primeRoot_not_mem_of_isPurelyInseparable [IsPurelyInseparable K L]
    (x : L) (hx : x ∉ Set.range (algebraMap K L)) :
    ∃ y : L, ∃ a : K, y ^ p = algebraMap K L a ∧ y ∉ Set.range (algebraMap K L) := by
  classical
  let : CharP K p := (algebraMap K L).charP (algebraMap K L).injective p
  have hex : ∃ n : ℕ, x ^ p ^ n ∈ Set.range (algebraMap K L) := by
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem K p x
    exact ⟨n, a, ha⟩
  let n := Nat.find hex
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    have hmem := Nat.find_spec hex
    change x ^ p ^ n ∈ Set.range (algebraMap K L) at hmem
    exact hx (by simpa only [hn0, pow_zero, pow_one] using hmem)
  let y := x ^ p ^ (n - 1)
  have hy : y ∉ Set.range (algebraMap K L) :=
    Nat.find_min hex (Nat.sub_lt hn Nat.zero_lt_one)
  have hpow : y ^ p = x ^ p ^ n := by
    dsimp [y]
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_of_lt hn)]
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  exact ⟨y, a, hpow.trans ha.symm, hy⟩

omit [CharP L p] in
/-- 底体の外のp乗根を添加した中間体の標準生成元は、同じ関係式・非所属・生成条件を持つ。
次数の帰納と微分の帰納の両方で、Lの元を実際の中間体の元へ移すために使う。 -/
theorem primeRoot_adjoin_gen_properties
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) :
    (IntermediateField.AdjoinSimple.gen K x) ^ p =
        algebraMap K (IntermediateField.adjoin K {x}) a ∧
      IntermediateField.AdjoinSimple.gen K x ∉
        Set.range (algebraMap K (IntermediateField.adjoin K {x})) ∧
      Algebra.adjoin K {IntermediateField.AdjoinSimple.gen K x} = ⊤ := by
  let B := IntermediateField.adjoin.powerBasis (isIntegral_of_prime_pow_eq x a hpow)
  refine ⟨Subtype.ext hpow, ?_, B.adjoin_gen_eq_top⟩
  rintro ⟨c, hc⟩
  exact hx ⟨c, congrArg (fun t : IntermediateField.adjoin K {x} ↦ (t : L)) hc⟩

/-- 底体の外のp乗根を添加すると、残りの有限拡大の次数は厳密に減る。 -/
theorem finrank_over_primeRoot_adjoin_lt [Module.Finite K L]
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) :
    Module.finrank (IntermediateField.adjoin K {x}) L < Module.finrank K L := by
  rw [← Module.finrank_mul_finrank K (IntermediateField.adjoin K {x}) L,
    Nat.lt_mul_iff_one_lt_left Module.finrank_pos, finrank_adjoin_of_prime_pow_eq x a hpow hx]
  exact (Fact.out : p.Prime).one_lt

/-- 非自明な有限純非分離拡大で、次数pの添加と帰納のための厳密な次数減少を供給する。 -/
theorem exists_primeRoot_step_of_isPurelyInseparable [IsPurelyInseparable K L]
    [Module.Finite K L] (hne : ¬ Function.Surjective (algebraMap K L)) :
    ∃ x : L, ∃ a : K, x ^ p = algebraMap K L a ∧ x ∉ Set.range (algebraMap K L) ∧
      Module.finrank K (IntermediateField.adjoin K {x}) = p ∧
      Module.finrank (IntermediateField.adjoin K {x}) L < Module.finrank K L := by
  classical
  obtain ⟨z, hz⟩ := not_forall.mp hne
  obtain ⟨x, a, hpow, hx⟩ := exists_primeRoot_not_mem_of_isPurelyInseparable z hz
  exact ⟨x, a, hpow, hx, finrank_adjoin_of_prime_pow_eq x a hpow hx,
    finrank_over_primeRoot_adjoin_lt x a hpow hx⟩

end SerrePositivity
