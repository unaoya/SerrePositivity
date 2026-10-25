module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorial
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaDividedPowers
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionRawMinimal

/-! # A[1/p]内の階乗分母生成部分環とrawδ評価の像

実際の部分環とその生成元を比較する。逆包含にはδ安定性を明示する。
この入力の解消、分冪包の普遍性、CFFは別工程。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A[1/p]内の正規化されたy_s^n/n!。非p倍の単元性は利用時に明示する。 -/
def pDivisionFactorialValue (p : ℕ) (y : σ → A) (s : σ) (n : ℕ) :
    Localization.Away (p : A) :=
  Ring.inverse (n.factorial : Localization.Away (p : A)) *
    (algebraMap A (Localization.Away (p : A)) (y s)) ^ n

/-- Aとすべての階乗分母y_s^n/n!で生成される具体的な局所化内部分環。 -/
def pDivisionFactorialSubring (p : ℕ) (y : σ → A) : Subring (Localization.Away (p : A)) :=
  Subring.closure (Set.range (algebraMap A (Localization.Away (p : A))) ∪
    Set.range (fun z : σ × ℕ ↦ pDivisionFactorialValue p y z.1 z.2))

omit [Fact p.Prime] in
/-- 元のAの像は階乗生成部分環に入る。 -/
theorem pDivisionFactorialSubring_coeff_mem (y : σ → A) (r : A) :
    algebraMap A (Localization.Away (p : A)) r ∈ pDivisionFactorialSubring p y :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

omit [Fact p.Prime] in
/-- 正規化された各階乗分母は、定義した生成部分環に入る。 -/
theorem pDivisionFactorialSubring_value_mem (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialValue p y s n ∈ pDivisionFactorialSubring p y :=
  Subring.subset_closure (Or.inr ⟨(s, n), rfl⟩)

/-- raw包で選んだ階乗分母の実局所化像は、局所化内の正規化された階乗分母。 -/
theorem deltaPDivisionToAway_factorialQuotient (D : DeltaStructure p A) (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))
      (deltaPDivisionRawFactorialQuotient D y hlocal s n) =
        pDivisionFactorialValue p y s n := by
  let f := deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))
  have h := congrArg f (deltaPDivisionRawFactorialQuotient_spec D y hlocal s n)
  simp only [map_mul, map_natCast, map_pow] at h
  have hb := RingHom.congr_fun (deltaPDivisionToAway_spec D
    (fun s ↦ D.frobeniusLift (y s))).2.1 (y s)
  change f (deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) (y s)) = _ at hb
  rw [hb] at h
  change f _ = Ring.inverse _ * _
  rw [← h, Ring.inverse_mul_cancel_left _ _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial (Nat.factorial_ne_zero n))]

/-- 具体的な全階乗分母の生成部分環はrawδ評価の実像に含まれる。 -/
theorem pDivisionFactorialSubring_le_raw_range (D : DeltaStructure p A) (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    pDivisionFactorialSubring p y ≤
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range := by
  apply Subring.closure_le.mpr
  rintro t (⟨r, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
  · exact ⟨deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) r,
      RingHom.congr_fun (deltaPDivisionToAway_spec D (fun s ↦ D.frobeniusLift (y s))).2.1 r⟩
  · exact ⟨deltaPDivisionRawFactorialQuotient D y hlocal s n,
      deltaPDivisionToAway_factorialQuotient D y hlocal s n⟩

/-- y_s^p/pは(p−1)!倍のp番目の階乗分母として生成部分環に入る。 -/
theorem pDivisionFactorialSubring_pow_div_prime_mem (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    IsLocalization.Away.invSelf (p : A) *
      (algebraMap A (Localization.Away (p : A)) (y s)) ^ p ∈ pDivisionFactorialSubring p y := by
  let L := Localization.Away (p : A)
  have hp : IsUnit (p : L) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := L) (p : A)
  have hinv : (p : L) * Ring.inverse (p.factorial : L) * ((p - 1).factorial : L) = 1 := by
    calc
      _ = (p.factorial : L) * Ring.inverse (p.factorial : L) := by
        rw [← Nat.mul_factorial_pred (Fact.out : p.Prime).ne_zero, Nat.cast_mul]
        ring
      _ = 1 := Ring.mul_inverse_cancel _
        (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal p.factorial
          (Nat.factorial_ne_zero p))
  have he : IsLocalization.Away.invSelf (p : A) * (algebraMap A L (y s)) ^ p =
      ((p - 1).factorial : L) * pDivisionFactorialValue p y s p := by
    apply hp.mul_left_cancel
    change (p : L) * (_ * _) = (p : L) * (_ * (Ring.inverse _ * _))
    rw [← mul_assoc, ← map_natCast (algebraMap A L), IsLocalization.Away.mul_invSelf, one_mul]
    calc
      _ = (1 : L) * (algebraMap A L (y s)) ^ p := (one_mul _).symm
      _ = _ := by rw [← hinv, map_natCast]; ring
  rw [he]
  apply (pDivisionFactorialSubring p y).mul_mem
  · simpa only [map_natCast] using
      pDivisionFactorialSubring_coeff_mem (p := p) y ((p - 1).factorial : A)
  · exact pDivisionFactorialSubring_value_mem y s p

/-- 生成部分環のδ安定性を供給すれば、rawδ評価の像との一致が従う。 -/
theorem pDivisionFactorialSubring_eq_raw_range_of_delta_stable (D : DeltaStructure p A)
    (y : σ → A) (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hδ : ∀ t ∈ pDivisionFactorialSubring p y,
      (deltaPDivisionAwayStructure D).delta t ∈ pDivisionFactorialSubring p y) :
    pDivisionFactorialSubring p y =
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range := by
  apply le_antisymm (pDivisionFactorialSubring_le_raw_range D y hlocal)
  exact deltaPDivisionToAway_range_le_of_delta_stable D y _
    (pDivisionFactorialSubring_coeff_mem y)
    (pDivisionFactorialSubring_pow_div_prime_mem y hlocal) hδ

end SerrePositivity.BhattScholze
