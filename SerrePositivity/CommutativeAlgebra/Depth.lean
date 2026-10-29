module

public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import SerrePositivity.CommutativeAlgebra.AssociatedPrimeQuotient
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Regular.Category

/-! # 深さと随伴素イデアル

## 概要

Noether 局所環 `R` 上の有限生成加群 `M` について：
- 素イデアル `p < q` なら `dim R/q + 1 ≤ dim R/p`（`ringKrullDim_quotient_succ_le_of_lt`）。
- `M` の弱正則列の長さは、`M` の任意の随伴素イデアル `p` について `dim R/p` 以下
  （`length_isWeaklyRegular_le_dim_associatedPrime`）。したがって `depth M ≤ dim R/p`
  （`depth_le_dim_quotient_of_mem_associatedPrimes`、Matsumura Thm 17.2）。
- 正則元 `x` で割ると深さは高々一つ下がり（`depth_le_depth_quotSMulTop_add_one`）、
  弱正則列 `rs` で割ると `depth M ≤ depth M/(rs)M + |rs|`（`depth_le_depth_quotient_add_length`）。

## 方針

正則元で割ると、随伴素イデアルはそれを真に含む商の随伴素イデアルに移る
（`exists_associatedPrime_quotSMulTop_gt`）ので、商の次元が一つずつ下がる。深さの不等式は
Mathlib の短完全列の深さの補題（`ModuleCat.depth_min_snd_fst_sub_one_le_trd_right`）による。

## 規約

深さは Mathlib の `IsLocalRing.depth`。商の深さの補題は有限生成性・Noether 性を要求しない。

## 使われ方

正則局所環の非混合性（`Unmixedness`）と、正則性の判定（`RegularLocalCriterion`）。
Mathlib への提出候補（mathlib-upstream の G9）。
-/

@[expose] public section

universe u

namespace SerrePositivity

open IsLocalRing RingTheory.Sequence

section AssociatedPrime

/-- Strict inclusion of prime ideals decreases quotient dimension by at least one. -/
theorem ringKrullDim_quotient_succ_le_of_lt
    {R : Type u} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p < q) : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := Set.exists_of_ssubset
    (show (p : Set R) ⊂ q from hpq)
  apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le)
    (r := Ideal.Quotient.mk p x)
  · apply mem_nonZeroDivisors_of_ne_zero
    exact fun hx => hxp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
  · change Ideal.Quotient.mk q x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxq

/-- The induction deriving the sequence length bound from the associated-prime
transition for quotienting by a regular element. -/
theorem length_isWeaklyRegular_le_dim_associatedPrime_of_transition
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hstep : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      {p : Ideal R}, p ∈ associatedPrimes R M → ∀ (x : R),
      x ∈ maximalIdeal R → IsSMulRegular M x →
      ∃ q : Ideal R, q ∈ associatedPrimes R (QuotSMulTop x M) ∧ p < q)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    let : p.IsPrime := hp.isPrime
    simpa only [List.length_nil, Nat.cast_zero] using
      (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p))
  | cons x rs ih =>
    obtain ⟨hxreg, htail⟩ := (isWeaklyRegular_cons_iff M x rs).mp hrs
    obtain ⟨q, hq, hpq⟩ := hstep M hp x (hmem x List.mem_cons_self) hxreg
    let : p.IsPrime := hp.isPrime
    let : q.IsPrime := hq.isPrime
    have htailmem : ∀ r ∈ rs, r ∈ maximalIdeal R :=
      fun r hr => hmem r (List.mem_cons_of_mem _ hr)
    have hlen := ih (M := QuotSMulTop x M) htail htailmem hq
    calc
      ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := add_le_add hlen le_rfl
      _ ≤ ringKrullDim (R ⧸ p) := ringKrullDim_quotient_succ_le_of_lt hpq

/-- A regular sequence contained in the maximal ideal has length at most the
dimension of every associated-prime quotient of the module. -/
theorem length_isWeaklyRegular_le_dim_associatedPrime
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  apply length_isWeaklyRegular_le_dim_associatedPrime_of_transition ?_ rs hrs hmem hp
  intro N _ _ _ q hq x hx hreg
  exact exists_associatedPrime_quotSMulTop_gt hq hx hreg

/-- Depth is at most the dimension of any associated-prime quotient. The
associated-prime hypothesis itself ensures that the module is nonzero. -/
theorem depth_le_dim_quotient_of_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (IsLocalRing.depth M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  let : p.IsPrime := hp.isPrime
  let : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with h | h
    · exact False.elim (not_isAssociatedPrime_of_subsingleton hp)
    · exact h
  have hdnonbot : ringKrullDim (R ⧸ p) ≠ ⊥ := by
    intro h
    have hzero := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
    simp [h] at hzero
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdnonbot
  rw [← hd]
  apply WithBot.coe_le_coe.mpr
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  have hlen := length_isWeaklyRegular_le_dim_associatedPrime rs hrs.1 hmem hp
  rw [← hd] at hlen
  exact_mod_cast hlen

end AssociatedPrime

section Quotient

open CategoryTheory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- 正則元による商では深さは高々一つしか下がらない。零加群・無限深さも含む。 -/
theorem depth_le_depth_quotSMulTop_add_one
    (M : Type u) [AddCommGroup M] [Module R M] (x : R) (hx : IsSMulRegular M x) :
    IsLocalRing.depth (ModuleCat.of R M) ≤
      IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 := by
  let N := ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))
  have h := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right N
    ((ModuleCat.of R M).smulShortComplex x) hx.smulShortComplex_shortExact
  change IsLocalRing.depth (ModuleCat.of R M) ⊓
      (IsLocalRing.depth (ModuleCat.of R M) - 1) ≤
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) at h
  rw [inf_of_le_right tsub_le_self] at h
  exact tsub_le_iff_right.mp h

/-- 弱正則列による商の深さと列の長さの和は、元の加群の深さ以上である。
有限生成性・Noether 性を要求しない。 -/
theorem depth_le_depth_quotient_add_length
    (M : Type u) [AddCommGroup M] [Module R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R M) ≤
      IsLocalRing.depth (ModuleCat.of R
        (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) + rs.length := by
  induction rs generalizing M with
  | nil =>
      rw [Ideal.ofList_nil, Submodule.bot_smul, List.length_nil, Nat.cast_zero, add_zero]
      exact (IsLocalRing.depth_eq_of_linearEquiv
        (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl)).symm.le
  | cons x rs ih =>
      obtain ⟨hx, htail⟩ := (isWeaklyRegular_cons_iff M x rs).mp hrs
      have hstep := depth_le_depth_quotSMulTop_add_one M x hx
      have hnext : IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 ≤
          (IsLocalRing.depth (ModuleCat.of R
            (QuotSMulTop x M ⧸ (Ideal.ofList rs • ⊤ : Submodule R (QuotSMulTop x M)))) +
            rs.length) + 1 := add_le_add (ih (QuotSMulTop x M) htail) le_rfl
      have h := hstep.trans hnext
      rw [← IsLocalRing.depth_eq_of_linearEquiv
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs)] at h
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc] using h

end Quotient

end SerrePositivity
