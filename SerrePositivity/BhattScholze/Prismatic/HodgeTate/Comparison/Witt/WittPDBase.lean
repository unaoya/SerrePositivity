module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDFromGenerators
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.InitTail
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Witt 基底の分冪イデアル

## 概要
第 0 Witt 成分が p の倍数である Witt ベクトルに分冪を入れ、第 0 成分への射と照合する。

## 方針
イデアルを Verschiebung の像と p で生成する。階乗分母を生成元上で計算し、
p を反転した環から分冪を制限する。

## 規約
係数環は p 正則とし、p と互いに素な自然数の可逆性を明示する。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 基底上の結晶模型。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open WittVector

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]

local notation "W" => WittVector p C

/-- 第 0 Witt 成分を取る環射。 -/
abbrev wZero : W →+* C := WittVector.constantCoeff

/-- 第 0 Witt 成分が p の倍数である元のイデアル。 -/
@[expose] def wittPdIdeal : Ideal W := (Ideal.span {(p : C)}).comap (wZero p C)

theorem p_mem_wittPdIdeal : (p : W) ∈ wittPdIdeal p C := by
  change wZero p C (p : W) ∈ Ideal.span {(p : C)}
  rw [map_natCast]
  exact Ideal.subset_span (Set.mem_singleton _)

private theorem exists_verschiebung_of_coeff_zero (x : W) (hx : x.coeff 0 = 0) :
    ∃ y : W, verschiebung y = x := by
  refine ⟨WittVector.mk p (fun i => x.coeff (i + 1)), ?_⟩
  ext i
  cases i with
  | zero => simpa only [verschiebung_coeff_zero] using hx.symm
  | succ i => rfl

private def wittPdGenerators : Set W := insert (p : W) (Set.range (verschiebung : W → W))

private theorem wittPdIdeal_eq_span :
    wittPdIdeal p C = Ideal.span (wittPdGenerators p C) := by
  apply le_antisymm
  · intro x hx
    change wZero p C x ∈ Ideal.span {(p : C)} at hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
    let b := teichmuller p a
    have hb : wZero p C b = a := teichmuller_coeff_zero p a
    have hx' : (x - (p : W) * b).coeff 0 = 0 := by
      change wZero p C (x - (p : W) * b) = 0
      rw [map_sub, map_mul, map_natCast, hb, ha, sub_self]
    obtain ⟨v, hv⟩ := exists_verschiebung_of_coeff_zero p C _ hx'
    have hs : (p : W) * b ∈ Ideal.span (wittPdGenerators p C) :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    have ht : verschiebung v ∈ Ideal.span (wittPdGenerators p C) :=
      Ideal.subset_span (Set.mem_insert_of_mem _ ⟨v, rfl⟩)
    rw [hv] at ht
    simpa only [sub_add_cancel] using Ideal.add_mem _ ht hs
  · rw [Ideal.span_le]
    rintro x (hx | ⟨v, rfl⟩)
    · obtain rfl := hx
      exact p_mem_wittPdIdeal p C
    · change (verschiebung v).coeff 0 ∈ Ideal.span {(p : C)}
      rw [verschiebung_coeff_zero]
      exact Ideal.zero_mem _

section NatUnit

variable (m : ℕ) (u : Cˣ)

private def natDivideHead (x : W) : C := ↑u⁻¹ * x.coeff 0

private def natDivideTail (x : W) : W :=
  WittVector.mk p (fun i => (x - (m : W) * teichmuller p (natDivideHead p C u x)).coeff (i + 1))

private theorem natDivideTail_eq (hu : (u : C) = (m : C)) (x : W) :
    verschiebung (natDivideTail p C m u x) =
      x - (m : W) * teichmuller p (natDivideHead p C u x) := by
  ext i
  cases i with
  | zero =>
    rw [verschiebung_coeff_zero]
    change 0 = wZero p C (x - (m : W) * teichmuller p (natDivideHead p C u x))
    rw [map_sub, map_mul, map_natCast, show wZero p C (teichmuller p (natDivideHead p C u x)) =
      natDivideHead p C u x from teichmuller_coeff_zero p _]
    rw [natDivideHead, ← hu, Units.mul_inv_cancel_left]
    change 0 = x.coeff 0 - x.coeff 0
    rw [sub_self]
  | succ i => rfl

private def natDivide (x : W) : W :=
  WittVector.mk p (fun n => natDivideHead p C u ((natDivideTail p C m u)^[n] x))

private theorem natDivide_split (x : W) :
    natDivide p C m u x =
      teichmuller p (natDivideHead p C u x) +
        verschiebung (natDivide p C m u (natDivideTail p C m u x)) := by
  ext i
  rw [WittVector.coeff_add_of_disjoint i _ _ (fun j => by
    cases j with
    | zero => exact Or.inr (verschiebung_coeff_zero _)
    | succ j => exact Or.inl (teichmuller_coeff_pos p _ (j + 1) (Nat.succ_pos j)))]
  cases i with
  | zero => rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]; rfl
  | succ i =>
    rw [teichmuller_coeff_pos p _ (i + 1) (Nat.succ_pos i), verschiebung_coeff_succ, zero_add]
    change natDivideHead p C u ((natDivideTail p C m u)^[i + 1] x) =
      natDivideHead p C u ((natDivideTail p C m u)^[i] (natDivideTail p C m u x))
    rw [Function.iterate_succ_apply]

/-- 係数環で可逆な自然数は Witt 環でも可逆。 -/
theorem witt_isUnit_natCast (hm : IsUnit (m : C)) : IsUnit (m : W) := by
  obtain ⟨v, hv⟩ := hm
  let E (x : W) := (m : W) * natDivide p C m v x - x
  have he (x : W) : E x = verschiebung (E (natDivideTail p C m v x)) := by
    rw [show E x = (m : W) * natDivide p C m v x - x from rfl, natDivide_split, mul_add]
    change _ = verschiebung ((m : W) * natDivide p C m v (natDivideTail p C m v x) -
      natDivideTail p C m v x)
    have hmV (y : W) : verschiebung ((m : W) * y) = (m : W) * verschiebung y := by
      simp only [← nsmul_eq_mul, map_nsmul]
    rw [map_sub, hmV, natDivideTail_eq p C m v hv]
    abel
  have hz (i : ℕ) (x : W) : (E x).coeff i = 0 := by
    induction i generalizing x with
    | zero => rw [he, verschiebung_coeff_zero]
    | succ i hi => rw [he, verschiebung_coeff_succ, hi]
  have hone : E 1 = 0 := by ext i; rw [hz, zero_coeff]
  exact IsUnit.of_mul_eq_one _ (sub_eq_zero.mp hone)

end NatUnit

variable (hpC : Function.Injective (fun x : C => (p : C) * x))

include hpC in
/-- Witt 環の p 正則性を係数環の p 正則性から得る。 -/
theorem witt_mul_prime_injective : Function.Injective (fun x : W => (p : W) * x) := by
  intro x y h
  apply witt_ghostMap_injective_of_mul_prime_injective p C hpC
  funext i
  apply hpC
  have hi := congrArg (ghostComponent i : W →+* C) h
  simpa only [map_mul, map_natCast, ghostMap_apply] using hi

include hpC in
private theorem verschiebung_pow (x : W) (n : ℕ) (hn : n ≠ 0) :
    (verschiebung x) ^ n = (p : W) ^ (n - 1) * verschiebung (x ^ n) := by
  apply witt_ghostMap_injective_of_mul_prime_injective p C hpC
  funext i
  cases i with
  | zero =>
    simp only [ghostMap_apply, map_pow, map_mul, map_natCast, ghostComponent_zero_verschiebung,
      zero_pow hn, mul_zero]
  | succ i =>
    simp only [ghostMap_apply, map_pow, map_mul, map_natCast, ghostComponent_verschiebung,
      mul_pow, ← mul_assoc, ← pow_succ]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]

section Factorial

variable {R : Type u} [CommRing R]

private theorem factorial_dvd_prime_pow_pred
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) {n : ℕ} (hn : n ≠ 0) :
    ∃ t : R, (n.factorial : R) * t = (p : R) ^ (n - 1) := by
  obtain ⟨j, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hj : padicValNat p n.factorial = j := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hj' : j ≤ n - 1 := by
    have h := padicValNat_factorial_lt_of_ne_zero p hn
    omega
  obtain ⟨v, hv⟩ := hlocal m hm
  refine ⟨(v⁻¹ : Rˣ) * (p : R) ^ (n - 1 - j), ?_⟩
  rw [hfac, Nat.cast_mul, Nat.cast_pow, ← hv, mul_assoc, Units.mul_inv_cancel_left,
    ← pow_add, Nat.add_sub_of_le hj']

omit [Fact p.Prime] in
private theorem away_injective_of_prime
    (hpR : Function.Injective (fun x : R => (p : R) * x)) :
    Function.Injective (algebraMap R (Localization.Away (p : R))) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : R))
    (S := Localization.Away (p : R))).mpr
  rintro ⟨z, hz⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff z (p : R)).mp hz
  have h : IsRegular (p : R) := ⟨hpR, fun x y e => hpR (by simpa only [mul_comm] using e)⟩
  exact h.pow n

private def pdOfFactorialLifts
    (hpR : Function.Injective (fun x : R => (p : R) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) (S : Set R)
    (hS : ∀ x ∈ S, ∀ n : ℕ, n ≠ 0 →
      ∃ y ∈ Ideal.span S, (n.factorial : R) * y = x ^ n) :
    DividedPowers (Ideal.span S) := by
  classical
  let L := Localization.Away (p : R)
  let f := algebraMap R L
  letI : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let γ := DividedPowers.RatAlgebra.dividedPowers ((Ideal.span S).map f)
  apply dividedPowersOfInjectiveSpan f S γ _ (away_injective_of_prime p hpR)
  intro x hx n hn
  obtain ⟨y, hy, h⟩ := hS x hx n hn
  refine ⟨y, hy, ?_⟩
  apply (IsUnit.natCast_factorial_of_algebra ℚ n (A := L)).mul_left_cancel
  rw [γ.factorial_mul_dpow_eq_pow (Ideal.mem_map_of_mem f (Ideal.subset_span hx))]
  simpa only [map_mul, map_natCast, map_pow] using congrArg f h

/-- p 正則な p 局所環で、p が生成するイデアル上の標準分冪。 -/
def residuePdStructure
    (hpR : Function.Injective (fun x : R => (p : R) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) :
    DividedPowers (Ideal.span {(p : R)}) := by
  apply pdOfFactorialLifts p hpR hlocal
  rintro _ rfl n hn
  obtain ⟨t, ht⟩ := factorial_dvd_prime_pow_pred p hlocal hn
  refine ⟨t * p, Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)), ?_⟩
  rw [← mul_assoc, ht, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]

end Factorial

/-- 第 0 成分が p の倍数である Witt ベクトルのイデアル上の分冪。 -/
def wittPdStructure (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C)) :
    DividedPowers (wittPdIdeal p C) := by
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : W) :=
    witt_isUnit_natCast p C m (hlocalC m hm)
  rw [wittPdIdeal_eq_span]
  apply pdOfFactorialLifts p (witt_mul_prime_injective p C hpC) hlocal
  rintro x (hx | ⟨v, rfl⟩) n hn
  · obtain rfl := hx
    obtain ⟨t, ht⟩ := factorial_dvd_prime_pow_pred p hlocal hn
    refine ⟨t * p, Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)), ?_⟩
    rw [← mul_assoc, ht, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  · obtain ⟨t, ht⟩ := factorial_dvd_prime_pow_pred p hlocal hn
    refine ⟨t * verschiebung (v ^ n), Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨v ^ n, rfl⟩)), ?_⟩
    rw [← mul_assoc, ht, verschiebung_pow p C hpC v n hn]

/-- 第 0 成分環射は Witt 基底の分冪を係数環上の標準分冪へ送る。 -/
theorem wZero_isDPMorphism
    (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C)) :
    (wittPdStructure p C hpC hlocalC).IsDPMorphism (residuePdStructure p hpC hlocalC)
      (wZero p C) := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr le_rfl, fun {n} x hx => ?_⟩
  let L := Localization.Away (p : C)
  let f := algebraMap C L
  let : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocalC
  apply away_injective_of_prime p hpC
  apply (IsUnit.natCast_factorial_of_algebra ℚ n (A := L)).mul_left_cancel
  have h₁ := (residuePdStructure p hpC hlocalC).factorial_mul_dpow_eq_pow (n := n)
    (show wZero p C x ∈ Ideal.span {(p : C)} from hx)
  have h₂ := (wittPdStructure p C hpC hlocalC).factorial_mul_dpow_eq_pow (n := n) hx
  have h₁' := congrArg f h₁
  have h₂' := congrArg (f.comp (wZero p C)) h₂
  simp only [map_mul, map_natCast, map_pow] at h₁' h₂'
  exact h₁'.trans h₂'.symm

end SerrePositivity.BhattScholze.Prismatic
