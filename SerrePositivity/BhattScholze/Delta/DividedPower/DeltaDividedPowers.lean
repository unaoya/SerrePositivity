module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaDividedPowerIdeal
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.Localization.Rat
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # p局所・p正則δ環の具体的な分冪構造

Mathlibの有理代数上の分冪構造を標準p局所化の単射に沿って引き戻す。
分冪構造の定義と引戻しは既存APIを再利用する。分冪包の普遍性は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p局所環のp局所化では、非零自然数の像は単元。 -/
theorem primeDividedPowersAwayNat_isUnit
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n : ℕ) (hn : n ≠ 0) :
    IsUnit (n : Localization.Away (p : A)) := by
  obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  have hp : IsUnit (p : Localization.Away (p : A)) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (p : A)) (p : A)
  have hm' : IsUnit (m : Localization.Away (p : A)) := by
    simpa only [map_natCast] using (hlocal m hm).map (algebraMap A (Localization.Away (p : A)))
  rw [he, Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow k).mul hm'

/-- p局所環のp局所化に、既存の有理数の局所化普遍性で与えるℚ作用。 -/
@[instance_reducible] def primeDividedPowersAwayRatAlgebra
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    Algebra ℚ (Localization.Away (p : A)) := by
  let L := Localization.Away (p : A)
  have hZ : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom L z) := by
    intro z
    have hz : (z : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp z.property
    rcases z with ⟨z, hz'⟩
    cases z with
    | ofNat n =>
        change (Int.ofNat n) ≠ 0 at hz
        exact primeDividedPowersAwayNat_isUnit hlocal n (fun hn ↦ hz (congrArg Int.ofNat hn))
    | negSucc n =>
        change IsUnit (-(n + 1 : L))
        exact (primeDividedPowersAwayNat_isUnit hlocal (n + 1) (Nat.succ_ne_zero n)).neg
  exact (IsLocalization.lift (S := ℚ) hZ).toAlgebra

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
