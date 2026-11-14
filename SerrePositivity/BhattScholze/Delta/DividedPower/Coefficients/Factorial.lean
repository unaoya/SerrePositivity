module
public import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialCoefficients

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.Localization.Rat
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# δ 環の階乗分母と分冪構造（BS 著者版 Lemma 2.35・BS 著者版 Lemma 2.36 の係数）

## 概要
δ 環で反復 p 除算から p 典型の分母を作り、x^{pⁿ}/pⁿ! 型の階乗分母の可除性（BS 著者版 Lemma 2.35）を示す。p 除算可能イデアルが階乗分母で閉じること、分冪展開係数の恒等式と p 整性（BS 著者版 Lemma 2.36 の証明の計算）、p 局所・p 正則な δ 環の具体的な分冪構造。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`、`Andre/PowerRootEnvelope/DividedPowerPrime`、`Delta/DividedPower/PDivision`。
-/

universe u

/-! ## BS 著者版 Lemma 2.36の分冪展開係数のp可積分性

著者公開版p.23の係数をpで割った値について、既存p進付値で評価する。
分冪生成部分環のδ安定性への数論的入力。
-/

@[expose] public noncomputable section DeltaDividedPowerCoefficients

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]

/-- φ(y^n/n!)/pのi番目の分冪展開係数。 -/
def dividedPowerFrobeniusCoefficient (p n i : ℕ) : ℚ :=
  ((p * i).factorial : ℚ) / (i.factorial : ℚ) *
    ((p : ℚ) ^ (n - i) / ((n - i).factorial : ℚ)) / (p : ℚ)

/-- (y^n/n!)^p/pをγ_(pn)(y)で書く際の係数。 -/
def dividedPowerPowerCoefficient (p n : ℕ) : ℚ :=
  ((p * n).factorial : ℚ) / ((n.factorial : ℚ) ^ p * (p : ℚ))

/-- Frobenius展開係数のp進付値の正確な式。 -/
theorem dividedPowerFrobeniusCoefficient_valuation (n i : ℕ) (hi : i ≤ n) :
    padicValRat p (dividedPowerFrobeniusCoefficient p n i) =
      (n : ℤ) - padicValNat p (n - i).factorial - 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerFrobeniusCoefficient,
    padicValRat.div (mul_ne_zero (div_ne_zero (hf _) (hf _))
      (div_ne_zero (pow_ne_zero _ hp) (hf _))) hp,
    padicValRat.mul (div_ne_zero (hf _) (hf _)) (div_ne_zero (pow_ne_zero _ hp) (hf _)),
    padicValRat.div (hf _) (hf _), padicValRat.div (pow_ne_zero _ hp) (hf _)]
  simp only [padicValRat.of_nat, padicValRat.pow, padicValNat_self,
    padicValNat_factorial_mul]
  push_cast
  omega

/-- 正次数のFrobenius展開係数をpで割ってもp可積分。 -/
theorem dividedPowerFrobeniusCoefficient_valuation_nonneg (n i : ℕ)
    (hn : n ≠ 0) (hi : i ≤ n) :
    0 ≤ padicValRat p (dividedPowerFrobeniusCoefficient p n i) := by
  rw [dividedPowerFrobeniusCoefficient_valuation n i hi]
  have hb : padicValNat p (n - i).factorial < n := by
    by_cases h : n - i = 0
    · simpa [h] using Nat.pos_of_ne_zero hn
    · exact lt_of_lt_of_le (padicValNat_factorial_lt_of_ne_zero p h) (Nat.sub_le n i)
  omega

/-- 冪の展開係数のp進付値の正確な式。 -/
theorem dividedPowerPowerCoefficient_valuation (n : ℕ) :
    padicValRat p (dividedPowerPowerCoefficient p n) =
      (n : ℤ) - (p - 1 : ℕ) * padicValNat p n.factorial - 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerPowerCoefficient,
    padicValRat.div (hf _) (mul_ne_zero (pow_ne_zero _ (hf _)) hp),
    padicValRat.mul (pow_ne_zero _ (hf _)) hp]
  simp only [padicValRat.of_nat, padicValRat.pow, padicValNat_self,
    padicValNat_factorial_mul]
  have hp1 := (Fact.out : p.Prime).one_lt
  push_cast [Nat.cast_sub (Nat.one_le_of_lt hp1)]
  ring

/-- 正次数の冪の展開係数をpで割ってもp可積分。 -/
theorem dividedPowerPowerCoefficient_valuation_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ padicValRat p (dividedPowerPowerCoefficient p n) := by
  rw [dividedPowerPowerCoefficient_valuation]
  have hb := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn
  have hb' : (((p - 1) * padicValNat p n.factorial : ℕ) : ℤ) < n := by
    exact_mod_cast hb
  push_cast at hb'
  omega

/-- 非負p進付値を持つ有理数の既約分母はpで割れない。 -/
theorem prime_not_dvd_den_of_padicVal_nonneg (q : ℚ) (hq : 0 ≤ padicValRat p q) :
    ¬p ∣ q.den := by
  have hd : padicValNat p q.den = 0 := by
    rcases q.num_or_den_zero_padicVal (Fact.out : p.Prime) with hnum | hden
    · rw [padicValRat_def, hnum] at hq
      omega
    · exact hden
  intro hdiv
  have hpos := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
  omega

end SerrePositivity.BhattScholze

end DeltaDividedPowerCoefficients

/-! ## 分冪展開係数の恒等式

任意Q代数に移せる有理数の等式を先に示す。
-/

@[expose] public noncomputable section DeltaDividedPowerExpansion

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]

/-- 付値計算したFrobenius係数は、二項展開の実際の係数と一致する。 -/
theorem dividedPowerFrobeniusCoefficient_div_factorial (n i : ℕ) (hi : i ≤ n) :
    dividedPowerFrobeniusCoefficient p n i / ((p * i).factorial : ℚ) =
      (n.choose i : ℚ) * (p : ℚ) ^ (n - i) / ((p : ℚ) * (n.factorial : ℚ)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hc : (n.choose i : ℚ) * (i.factorial : ℚ) * ((n - i).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  rw [dividedPowerFrobeniusCoefficient]
  field_simp
  rw [← hc]
  ring

/-- 付値計算した冪の係数は、γ_(pn)(x)へ掛ける実際の係数と一致する。 -/
theorem dividedPowerPowerCoefficient_div_factorial (n : ℕ) :
    dividedPowerPowerCoefficient p n / ((p * n).factorial : ℚ) =
      1 / ((p : ℚ) * (n.factorial : ℚ) ^ p) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerPowerCoefficient]
  field_simp

/-- 有理係数の環射の下での、Frobenius型二項式の実際の分冪展開。 -/
theorem dividedPower_frobenius_expansion {R : Type u} [CommRing R]
    (f : ℚ →+* R) (x z : R) (n : ℕ) :
    f (1 / ((p : ℚ) * (n.factorial : ℚ))) * (x ^ p + f (p : ℚ) * z) ^ n =
      ∑ i ∈ Finset.range (n + 1), f (dividedPowerFrobeniusCoefficient p n i) *
        (f (1 / ((p * i).factorial : ℚ)) * x ^ (p * i)) * z ^ (n - i) := by
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hni : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcQ : 1 / ((p : ℚ) * (n.factorial : ℚ)) * (p : ℚ) ^ (n - i) * (n.choose i : ℚ) =
      dividedPowerFrobeniusCoefficient p n i * (1 / ((p * i).factorial : ℚ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using
      (dividedPowerFrobeniusCoefficient_div_factorial (p := p) n i hni).symm
  have hc := congrArg f hcQ
  simp only [map_mul, map_pow, map_natCast] at hc
  rw [mul_pow, ← pow_mul]
  simp only [map_natCast]
  calc
    _ = (f (1 / ((p : ℚ) * (n.factorial : ℚ))) * (p : R) ^ (n - i) *
        (n.choose i : R)) * x ^ (p * i) * z ^ (n - i) := by ring
    _ = _ := by rw [hc]; ring

/-- 有理係数の環射の下での、γ_n(x)^p/pの実際の分冪展開。 -/
theorem dividedPower_power_expansion {R : Type u} [CommRing R]
    (f : ℚ →+* R) (x : R) (n : ℕ) :
    f (1 / (p : ℚ)) * (f (1 / (n.factorial : ℚ)) * x ^ n) ^ p =
      f (dividedPowerPowerCoefficient p n) *
        (f (1 / ((p * n).factorial : ℚ)) * x ^ (p * n)) := by
  have hcQ : 1 / (p : ℚ) * (1 / (n.factorial : ℚ)) ^ p =
      dividedPowerPowerCoefficient p n * (1 / ((p * n).factorial : ℚ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_inv_rev, inv_pow,
      mul_comm, mul_left_comm, mul_assoc]
      using (dividedPowerPowerCoefficient_div_factorial (p := p) n).symm
  have hc := congrArg f hcQ
  simp only [map_mul, map_pow] at hc
  rw [mul_pow, ← pow_mul, Nat.mul_comm n p]
  calc
    _ = (f (1 / (p : ℚ)) * f (1 / (n.factorial : ℚ)) ^ p) * x ^ (p * n) := by ring
    _ = _ := by rw [hc]; ring

end SerrePositivity.BhattScholze

end DeltaDividedPowerExpansion

/-! ## δ環の反復p除算とp典型分母

BS 著者版 Lemma 2.35の代数的入力。一般のpねじれを許す。
階乗分母全体・分冪構造・分冪包との同定は別工程。
-/

@[expose] public noncomputable section DeltaDividedPowerStep

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ環でx^p=pzならz^pもpで割り切れる。p正則性は不要。 -/
theorem prime_dvd_divided_pow (D : DeltaStructure p A) {x z : A}
    (hx : x ^ p = (p : A) * z) : (p : A) ∣ z ^ p := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have h := D.map_delta_pow_prime_of_zero q hp x
  rw [hx, D.map_delta_mul_of_prime_zero q hp,
    D.map_delta_prime_of_zero q hp, hp, zero_pow (Fact.out : p.Prime).ne_zero,
    zero_mul, one_mul, zero_add] at h
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow] using h))

/-- 一度x^p/pが存在すれば、c_(n+1)=c_n^p/pを全段で選べる。 -/
theorem exists_iterated_prime_division (D : DeltaStructure p A) {x z : A}
    (hx : x ^ p = (p : A) * z) :
    ∃ c : ℕ → A, c 0 = x ∧ c 1 = z ∧ ∀ n, (p : A) * c (n + 1) = c n ^ p := by
  let T := {t : A // (p : A) ∣ t ^ p}
  let next : T → T := fun t =>
    ⟨t.property.choose, D.prime_dvd_divided_pow t.property.choose_spec⟩
  let c : ℕ → A := fun n => if n = 0 then x else
    ((next^[n - 1]) ⟨z, D.prime_dvd_divided_pow hx⟩).val
  refine ⟨c, by simp [c], by simp [c], ?_⟩
  intro n
  cases n with
  | zero => simpa [c] using hx.symm
  | succ n =>
      simp only [c, Nat.succ_ne_zero, ↓reduceIte,
        Nat.succ_sub_one, Function.iterate_succ_apply']
      exact ((next^[n]) ⟨z, D.prime_dvd_divided_pow hx⟩).property.choose_spec.symm

/-- p典型反復除算に現れるpの指数。 -/
def primeDivisionExponent (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => p * primeDivisionExponent p n + 1

omit [Fact p.Prime] in
/-- 反復除算列の各項は、p冪分母を払うとx^(p^n)となる。 -/
theorem iterated_prime_division_denominator {x : A} {c : ℕ → A}
    (h₀ : c 0 = x) (hc : ∀ n, (p : A) * c (n + 1) = c n ^ p) (n : ℕ) :
    (p : A) ^ primeDivisionExponent p n * c n = x ^ p ^ n := by
  induction n with
  | zero => simp [primeDivisionExponent, h₀]
  | succ n ih =>
      calc
        (p : A) ^ primeDivisionExponent p (n + 1) * c (n + 1) =
            (p : A) ^ (p * primeDivisionExponent p n) * ((p : A) * c (n + 1)) := by
          rw [primeDivisionExponent, pow_succ, mul_assoc]
        _ = ((p : A) ^ primeDivisionExponent p n * c n) ^ p := by
          rw [hc, mul_pow, ← pow_mul, Nat.mul_comm p]
        _ = x ^ p ^ (n + 1) := by rw [ih, ← pow_mul, Nat.pow_succ]

omit [Fact p.Prime] in
/-- p正則環では、同じ初項を持つ反復p除算列は一意。 -/
theorem iterated_prime_division_unique
    (hpA : Function.Injective (fun t : A => (p : A) * t)) {c d : ℕ → A}
    (h₀ : c 0 = d 0) (hc : ∀ n, (p : A) * c (n + 1) = c n ^ p)
    (hd : ∀ n, (p : A) * d (n + 1) = d n ^ p) : c = d := by
  funext n
  induction n with
  | zero => exact h₀
  | succ n ih =>
      apply hpA
      change (p : A) * c (n + 1) = (p : A) * d (n + 1)
      rw [hc, hd, ih]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaDividedPowerStep

/-! ## BS 著者版 Lemma 2.35の階乗分母の可除性

δ環のp除算閉性から、すべての階乗分母の存在を示す。
p局所性は非p倍の自然数が単元であるという仮定で明示する。
分冪構造の公理や分冪包との同定はここでは主張しない。
-/

@[expose] public noncomputable section DeltaFactorialDivision

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- x^pがpで割り切れるδ環では、p^val_p(n!)はx^nを割り切る。 -/
theorem factorial_valuation_pow_dvd (D : DeltaStructure p A) (n : ℕ) :
    ∀ x : A, (p : A) ∣ x ^ p → (p : A) ^ padicValNat p n.factorial ∣ x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · simp [hn]
      obtain ⟨z, hz⟩ := hx
      have hz' := D.prime_dvd_divided_pow hz
      have hk : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn)
        (Fact.out : p.Prime).one_lt
      obtain ⟨w, hw⟩ := ih (n / p) hk z hz'
      have he : padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p := by
        rw [← padicValNat_mul_div_factorial (p := p) n, padicValNat_factorial_mul]
      refine ⟨w * x ^ (n % p), ?_⟩
      calc
        x ^ n = (x ^ p) ^ (n / p) * x ^ (n % p) := by
          rw [← pow_mul, ← pow_add, Nat.div_add_mod]
        _ = ((p : A) * z) ^ (n / p) * x ^ (n % p) := by rw [hz]
        _ = (p : A) ^ padicValNat p n.factorial * (w * x ^ (n % p)) := by
          rw [mul_pow, hw, he, pow_add]
          ring

/-- 非p倍の自然数が単元であるδ環で、x^pのp除算から全階乗分母を得る（BS 著者版 Lemma 2.35 の p 局所の場合の階乗可除性）。 -/
theorem factorial_dvd_pow_of_prime_dvd_pow (D : DeltaStructure p A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {x : A}
    (hx : (p : A) ∣ x ^ p) (n : ℕ) : (n.factorial : A) ∣ x ^ n := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨w, hw⟩ := D.factorial_valuation_pow_dvd n x hx
  obtain ⟨v, hv⟩ := hlocal m hm
  refine ⟨(v⁻¹ : Aˣ) * w, ?_⟩
  rw [hw, hk, hfac, Nat.cast_mul, Nat.cast_pow, ← hv]
  simp only [mul_assoc, Units.mul_inv_cancel_left]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaFactorialDivision

/-! ## δ環のp除算可能イデアルと階乗分母の閉性

I={x | p∣x^p}を既存Frobenius liftの逆像イデアルとして具体化する。
正の次数の階乗分母をI内に選べることを示す。分冪公理は別工程。
-/

@[expose] public noncomputable section DeltaDividedPowerIdeal

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pで割れるp乗を持つ元のイデアル。 -/
def primeDividedPowerIdeal (D : DeltaStructure p A) : Ideal A :=
  Ideal.comap D.frobeniusLift (Ideal.span {(p : A)})

/-- Frobenius liftの逆像という定義はp∣x^pと同値。 -/
theorem mem_primeDividedPowerIdeal (D : DeltaStructure p A) (x : A) :
    x ∈ D.primeDividedPowerIdeal ↔ (p : A) ∣ x ^ p := by
  change D.frobeniusLift x ∈ Ideal.span {(p : A)} ↔ _
  rw [Ideal.mem_span_singleton, D.frobeniusLift_apply]
  exact dvd_add_left (dvd_mul_right (p : A) (D.delta x))

/-- 正の次数のp進階乗分母は、p除算可能イデアルの中に選べる。 -/
theorem exists_factorial_valuation_quotient_mem (D : DeltaStructure p A) (n : ℕ) :
    ∀ x : A, x ∈ D.primeDividedPowerIdeal → ∃ w : A,
      (p : A) ^ padicValNat p n.factorial * w = x ^ n ∧
      (n ≠ 0 → w ∈ D.primeDividedPowerIdeal) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · subst n
        exact ⟨1, by simp, by simp⟩
      obtain ⟨z, hz⟩ := (D.mem_primeDividedPowerIdeal x).mp hx
      have hzmem := (D.mem_primeDividedPowerIdeal z).mpr (D.prime_dvd_divided_pow hz)
      have hk : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn)
        (Fact.out : p.Prime).one_lt
      have he : padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p := by
        rw [← padicValNat_mul_div_factorial (p := p) n, padicValNat_factorial_mul]
      by_cases hk0 : n / p = 0
      · refine ⟨x ^ n, ?_, fun _ ↦ ?_⟩
        · simp [he, hk0]
        · exact (D.primeDividedPowerIdeal).pow_mem_of_mem hx n (Nat.pos_of_ne_zero hn)
      · obtain ⟨w, hw, hwmem⟩ := ih (n / p) hk z hzmem
        refine ⟨w * x ^ (n % p), ?_, fun _ ↦ ?_⟩
        · calc
            (p : A) ^ padicValNat p n.factorial * (w * x ^ (n % p)) =
                ((p : A) * z) ^ (n / p) * x ^ (n % p) := by
              rw [mul_pow, ← hw, he, pow_add]
              ring
            _ = x ^ n := by rw [← hz, ← pow_mul, ← pow_add, Nat.div_add_mod]
        · exact (D.primeDividedPowerIdeal).mul_mem_right _ (hwmem hk0)

/-- p局所性の下で、正の次数の階乗分母も同じイデアルに選べる（BS 著者版 Lemma 2.35 の p 局所の場合の階乗商の存在）。 -/
theorem exists_factorial_quotient_mem (D : DeltaStructure p A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {x : A}
    (hx : x ∈ D.primeDividedPowerIdeal) (n : ℕ) : ∃ w : A,
    (n.factorial : A) * w = x ^ n ∧ (n ≠ 0 → w ∈ D.primeDividedPowerIdeal) := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨w, hw, hwmem⟩ := D.exists_factorial_valuation_quotient_mem n x hx
  obtain ⟨v, hv⟩ := hlocal m hm
  refine ⟨(v⁻¹ : Aˣ) * w, ?_, fun hn ↦ ?_⟩
  · rw [← hw, hk, hfac, Nat.cast_mul, Nat.cast_pow, ← hv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  · exact (D.primeDividedPowerIdeal).mul_mem_left _ (hwmem hn)

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaDividedPowerIdeal

/-! ## p局所・p正則δ環の具体的な分冪構造

Mathlibの有理代数上の分冪構造を標準p局所化の単射に沿って引き戻す。
分冪構造の定義と引戻しは既存APIを再利用する。分冪包の普遍性は別工程。
-/

@[expose] public noncomputable section DeltaDividedPowers

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

omit [Fact p.Prime] in
private theorem away_injective
    (hpA : Function.Injective (fun t : A => (p : A) * t)) :
    Function.Injective (algebraMap A (Localization.Away (p : A))) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : A))
    (S := Localization.Away (p : A))).mpr
  intro c
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : A) (p : A)).mp c.property
  have hreg : IsRegular (p : A) := by
    refine ⟨hpA, ?_⟩
    intro x z h
    apply hpA
    change (p : A) * x = (p : A) * z
    simpa only [mul_comm] using h
  rw [← hn]
  exact hreg.pow n

/-- p局所・p正則δ環のI={x | p∣x^p}上の実際の分冪構造。 -/
def primeDividedPowers (D : DeltaStructure p A)
    (hpA : Function.Injective (fun t : A => (p : A) * t))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    DividedPowers D.primeDividedPowerIdeal := by
  classical
  let L := Localization.Away (p : A)
  let f := algebraMap A L
  letI : Algebra ℚ L := by exact primeDividedPowersAwayRatAlgebra hlocal
  let E := DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal L)
  have hI : D.primeDividedPowerIdeal.map f = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem
    · exact Ideal.mem_map_of_mem f ((D.mem_primeDividedPowerIdeal (p : A)).mpr
        (dvd_pow_self _ (Fact.out : p.Prime).ne_zero))
    · exact IsLocalization.Away.algebraMap_isUnit (S := L) (p : A)
  apply DividedPowers.ofInjective D.primeDividedPowerIdeal (⊤ : Ideal L) f
    (by exact away_injective hpA) E hI
  intro n x hx
  obtain ⟨w, hw, hwmem⟩ := D.exists_factorial_quotient_mem hlocal hx n
  refine ⟨w, hwmem, ?_⟩
  have hf := congrArg f hw
  simp only [map_mul, map_natCast, map_pow] at hf
  change f w = DividedPowers.RatAlgebra.dpow (⊤ : Ideal L) n (f x)
  rw [DividedPowers.RatAlgebra.dpow_eq_of_mem n (by trivial), ← hf,
    Ring.inverse_mul_cancel_left _ _ (IsUnit.natCast_factorial_of_algebra ℚ n)]

/-- この分冪構造は、階乗を掛けると通常の冪になる。 -/
theorem primeDividedPowers_factorial (D : DeltaStructure p A)
    (hpA : Function.Injective (fun t : A => (p : A) * t))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {x : A}
    (hx : x ∈ D.primeDividedPowerIdeal) (n : ℕ) :
    (n.factorial : A) * (D.primeDividedPowers hpA hlocal).dpow n x = x ^ n :=
  (D.primeDividedPowers hpA hlocal).factorial_mul_dpow_eq_pow hx


/-- p正則・p局所δ環のこのイデアル上の分冪構造は一意。 -/
theorem primeDividedPowers_unique (D : DeltaStructure p A)
    (hpA : Function.Injective (fun t : A => (p : A) * t))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (E : DividedPowers D.primeDividedPowerIdeal) : E = D.primeDividedPowers hpA hlocal := by
  let L := Localization.Away (p : A)
  let f := algebraMap A L
  let := primeDividedPowersAwayRatAlgebra hlocal
  apply DividedPowers.ext
  intro n x hx
  apply away_injective hpA
  apply (IsUnit.natCast_factorial_of_algebra ℚ n (A := L)).mul_left_cancel
  calc
    (n.factorial : L) * f (E.dpow n x) = f ((n.factorial : A) * E.dpow n x) := by
      rw [map_mul, map_natCast]
    _ = f (x ^ n) := congrArg f (E.factorial_mul_dpow_eq_pow hx)
    _ = f ((n.factorial : A) * (D.primeDividedPowers hpA hlocal).dpow n x) :=
      congrArg f (D.primeDividedPowers_factorial hpA hlocal hx n).symm
    _ = (n.factorial : L) * f ((D.primeDividedPowers hpA hlocal).dpow n x) := by
      rw [map_mul, map_natCast]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaDividedPowers

/-! ## 分冪展開のp可積分係数の実基底像

既約分母の単元逆数をA内で取り、標準局所化像の式を証明する。
ℚ作用は前工程の既存のものを用いる。p正則性は不要。
-/

@[expose] public noncomputable section DeltaDividedPowerCoefficientImage

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 非負p進付値の有理数の標準局所化像は、p局所環Aの基底像に入る。 -/
theorem primeLocalRat_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (q : ℚ)
    (hq : 0 ≤ padicValRat p q) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) q ∈
      (algebraMap A (Localization.Away (p : A))).range := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let L := Localization.Away (p : A)
  let f := algebraMap A L
  obtain ⟨v, hv⟩ := hlocal q.den (prime_not_dvd_den_of_padicVal_nonneg q hq)
  refine ⟨(v⁻¹ : Aˣ) * (q.num : A), ?_⟩
  have hdQ : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hqQ : (q.den : ℚ) * q = (q.num : ℚ) := by
    have h := (div_eq_iff hdQ).mp q.num_div_den
    simpa only [mul_comm] using h.symm
  have hqL := congrArg (algebraMap ℚ L) hqQ
  simp only [map_mul, map_natCast, map_intCast] at hqL
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal q.den q.den_ne_zero).mul_left_cancel
  calc
    (q.den : L) * f ((v⁻¹ : Aˣ) * (q.num : A)) =
        f ((q.den : A) * ((v⁻¹ : Aˣ) * (q.num : A))) := by simp only [map_mul, map_natCast]
    _ = f (q.num : A) := by rw [← hv, Units.mul_inv_cancel_left]
    _ = (q.den : L) * algebraMap ℚ L q := by rw [map_intCast, hqL]

/-- 正次数のFrobenius分冪展開係数の像はAの実標準像に入る。 -/
theorem dividedPowerFrobeniusCoefficient_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n i : ℕ)
    (hn : n ≠ 0) (hi : i ≤ n) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) (dividedPowerFrobeniusCoefficient p n i) ∈
      (algebraMap A (Localization.Away (p : A))).range :=
  primeLocalRat_mem_baseRange hlocal _
    (dividedPowerFrobeniusCoefficient_valuation_nonneg n i hn hi)

/-- 正次数の冪の分冪展開係数の像もAの実標準像に入る。 -/
theorem dividedPowerPowerCoefficient_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n : ℕ) (hn : n ≠ 0) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) (dividedPowerPowerCoefficient p n) ∈
      (algebraMap A (Localization.Away (p : A))).range :=
  primeLocalRat_mem_baseRange hlocal _ (dividedPowerPowerCoefficient_valuation_nonneg n hn)

end SerrePositivity.BhattScholze

end DeltaDividedPowerCoefficientImage

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.35"] _root_.SerrePositivity.BhattScholze.DeltaStructure.exists_factorial_quotient_mem
attribute [cite BS19 "Lemma 2.35"] _root_.SerrePositivity.BhattScholze.DeltaStructure.factorial_dvd_pow_of_prime_dvd_pow
