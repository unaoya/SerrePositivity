module

public import SerrePositivity.FieldTheory.PAdjoin
public import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-! # 純非分離拡大から次数pの段階を取り出す

底体の外の元について、底体へ入る最小のFrobenius冪（Mathlib の `IsPurelyInseparable.elemExponent`）を取る。
その一つ前の冪が非自明なp乗根となり、添加後の残りの拡大次数は厳密に減る。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP L p]

/-- 純非分離拡大の底体の外の元から、底体の外のp乗根を取り出す。拡大の有限性は不要。
`e` を `x` の指数（Mathlib の `IsPurelyInseparable.elemExponent`、`x ^ p ^ e` が底体に入る最小の `e`）として、
`x ^ p ^ (e - 1)` を取る。 -/
theorem exists_primeRoot_not_mem_of_isPurelyInseparable [IsPurelyInseparable K L]
    (x : L) (hx : x ∉ Set.range (algebraMap K L)) :
    ∃ y : L, ∃ a : K, y ^ p = algebraMap K L a ∧ y ∉ Set.range (algebraMap K L) := by
  let : CharP K p := (algebraMap K L).charP (algebraMap K L).injective p
  let : ExpChar K p := ExpChar.prime (Fact.out : p.Prime)
  have he : 0 < IsPurelyInseparable.elemExponent K x := by
    by_contra h
    apply hx
    simpa [Nat.eq_zero_of_not_pos h] using IsPurelyInseparable.elemExponent_def' K p x
  refine ⟨x ^ p ^ (IsPurelyInseparable.elemExponent K x - 1),
    IsPurelyInseparable.elemReduct K x, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel he,
      IsPurelyInseparable.algebraMap_elemReduct_eq' K p x]
  · simpa using IsPurelyInseparable.elemExponent_min' K p (Nat.sub_lt he Nat.zero_lt_one)

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

universe v in
/-- 有限な純非分離拡大についての、p 乗根の添加による帰納原理。
`L` 上の性質 `P K` が、`K → L` が全射のとき成り立ち、`K(x)`（`x ^ p ∈ K`、`x ∉ K`）で成り立てば `K` でも
成り立つなら、すべての有限な純非分離拡大 `K → L` で成り立つ。帰納は残りの拡大次数について行う。
`K` は `L` と同じ宇宙に置く（中間体 `K(x)` を次の底体として使うため）。 -/
theorem induction_on_primeRoot_of_isPurelyInseparable {L : Type v} [Field L]
    {p : ℕ} [Fact p.Prime] [CharP L p]
    (P : ∀ (K : Type v) [Field K] [Algebra K L], Prop)
    (base : ∀ (K : Type v) [Field K] [Algebra K L], Function.Surjective (algebraMap K L) → P K)
    (step : ∀ (K : Type v) [Field K] [Algebra K L] [CharP K p] [IsPurelyInseparable K L]
      [Module.Finite K L] (x : L) (a : K), x ^ p = algebraMap K L a →
      x ∉ Set.range (algebraMap K L) → P (IntermediateField.adjoin K {x}) → P K)
    (K : Type v) [Field K] [Algebra K L] [CharP K p] [IsPurelyInseparable K L]
    [Module.Finite K L] : P K := by
  generalize hd : Module.finrank K L = d
  induction d using Nat.strongRecOn generalizing K with
  | ind d IH =>
    by_cases hsurj : Function.Surjective (algebraMap K L)
    · exact base K hsurj
    obtain ⟨x, a, hxp, hx, _, hlt⟩ := exists_primeRoot_step_of_isPurelyInseparable hsurj
    let T := IntermediateField.adjoin K {x}
    let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
    let : IsPurelyInseparable T L := IsPurelyInseparable.tower_top K T L
    exact step K x a hxp hx (IH _ (hd ▸ hlt) T rfl)

end SerrePositivity
