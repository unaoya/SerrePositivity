module

public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialStructure

/-! # 既存分冪イデアルを持つ標的における階乗部分環

分冪の階乗恒等式で具体的部分環を基底の像へ同定する。
像の同定はpねじれを許す。環同型の構成時のみp正則性を要求する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 分冪イデアル内の元の階乗分母は、実分冪値の局所化像である。 -/
theorem pDivisionFactorialValue_eq_dpow_image
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I)
    (s : σ) (n : ℕ) :
    pDivisionFactorialValue p y s n =
      algebraMap A (Localization.Away (p : A)) (H.dpow n (y s)) := by
  have h := congrArg (algebraMap A (Localization.Away (p : A)))
    (H.factorial_mul_dpow_eq_pow (n := n) (hy s))
  simp only [map_mul, map_natCast, map_pow] at h
  rw [pDivisionFactorialValue, ← h, Ring.inverse_mul_cancel_left _ _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
      (Nat.factorial_ne_zero n))]

/-- 既に分冪イデアル内にある元族を添加しても、局所化内では基底の像に留まる。 -/
theorem pDivisionFactorialSubring_eq_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    pDivisionFactorialSubring p y = (algebraMap A (Localization.Away (p : A))).range := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro t (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · exact ⟨a, rfl⟩
    · exact ⟨H.dpow n (y s), (pDivisionFactorialValue_eq_dpow_image hlocal H y hy s n).symm⟩
  · rintro t ⟨a, rfl⟩
    exact pDivisionFactorialSubring_coeff_mem y a

/-- 分冪標的に対する基底射は、pねじれがあっても全射。 -/
theorem pDivisionFactorialBase_surjective_of_dividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    Function.Surjective (pDivisionFactorialBase p y) := by
  rintro ⟨t, ht⟩
  rw [pDivisionFactorialSubring_eq_baseRange hlocal H y hy] at ht
  obtain ⟨a, ha⟩ := ht
  exact ⟨a, Subtype.ext ha⟩

omit [Fact p.Prime] in
/-- p正則な基底では、階乗部分環への基底射も単射。 -/
theorem pDivisionFactorialBase_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : σ → A) :
    Function.Injective (pDivisionFactorialBase p y) := by
  have hi : Function.Injective (algebraMap A (Localization.Away (p : A))) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : A))
      (S := Localization.Away (p : A))).mpr
    intro c
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : A) (p : A)).mp c.property
    have hr : IsRegular (p : A) := ⟨hpA, by
      intro x z h
      apply hpA
      simpa only [mul_comm] using h⟩
    rw [← hn]
    exact hr.pow n
  intro x z h
  apply hi
  exact congrArg Subtype.val h

/-- p正則な既存分冪標的では、基底射自身が具体的階乗部分環との環同型を与える。 -/
def pDivisionFactorialBaseEquivOfDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    A ≃+* pDivisionFactorialSubring p y :=
  RingEquiv.ofBijective (pDivisionFactorialBase p y)
    ⟨pDivisionFactorialBase_injective hpA y,
      pDivisionFactorialBase_surjective_of_dividedPowers hlocal H y hy⟩

end SerrePositivity.BhattScholze
