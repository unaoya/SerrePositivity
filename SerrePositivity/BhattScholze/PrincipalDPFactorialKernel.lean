module

public import SerrePositivity.BhattScholze.PrincipalDPToFactorial

/-! # 一元表示環から階乗部分環への全射の核

核を実p局所化の核へ同定する。表示環のp正則性はこのファイルでは主張しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実全射で零になる元は、表示環をp局所化しても零になる。 -/
theorem principalDPToFactorial_ker_le_away_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (principalDPToFactorial hA D y) ≤
      RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) := by
  let R := PrincipalDPPresentation A y
  let L := Localization.Away (p : R)
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  have hpL : IsUnit (algebraMap A L (p : A)) := by
    have hp := IsLocalization.Away.algebraMap_isUnit (S := L) (p : R)
    have hc : algebraMap R L (p : R) = (p : L) := map_natCast (algebraMap R L) p
    rw [hc] at hp
    simpa only [map_natCast] using hp
  let g : Localization.Away (p : A) →+* L :=
    IsLocalization.Away.lift (p : A) hpL
  let F : R →ₐ[A] L :=
    { toRingHom := g.comp (S.subtype.comp (principalDPToFactorial hA D y))
      commutes' := by
        intro a
        change g (principalDPToFactorial hA D y (algebraMap A R a) : Localization.Away (p : A)) = _
        rw [principalDPToFactorial_coeff]
        exact IsLocalization.Away.lift_eq (p : A) hpL a }
  let q : R →ₐ[A] L := IsScalarTower.toAlgHom A R L
  have hR : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R) := by
    intro m hm
    simpa only [map_natCast] using (hA m hm).map (algebraMap A R)
  have hF : F = q := by
    apply principalDPHom_ext y
    intro n
    apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hR n.factorial
      (Nat.factorial_ne_zero n)).mul_left_cancel
    have h₁ := congrArg F (principalDPGenerator_factorial_mul y n)
    have h₂ := congrArg q (principalDPGenerator_factorial_mul y n)
    have hFn : F (n.factorial : R) = (n.factorial : L) := map_natCast F _
    have hqn : q (n.factorial : R) = (n.factorial : L) := map_natCast q _
    have hFy : F (algebraMap A R y) = algebraMap A L y := F.commutes y
    have hqy : q (algebraMap A R y) = algebraMap A L y := q.commutes y
    simp only [map_mul, map_pow, hFn, hqn] at h₁ h₂
    change (n.factorial : L) * F (principalDPGenerator y n) =
      F (algebraMap A R y) ^ n at h₁
    change (n.factorial : L) * q (principalDPGenerator y n) =
      q (algebraMap A R y) ^ n at h₂
    rw [hFy] at h₁
    rw [hqy] at h₂
    exact h₁.trans h₂.symm
  intro b hb
  have hb0 : principalDPToFactorial hA D y b = 0 := hb
  change q b = 0
  rw [← hF]
  change g ((principalDPToFactorial hA D y b : S) : Localization.Away (p : A)) = 0
  rw [hb0]
  exact map_zero g

/-- 階乗部分環のp正則性により、表示環のp冪ねじれは実全射で零になる。 -/
theorem principalDPToFactorial_away_ker_le_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) ≤
      RingHom.ker (principalDPToFactorial hA D y) := by
  let R := PrincipalDPPresentation A y
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  let F := principalDPToFactorial hA D y
  intro b hb
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (p : R)) (Localization.Away (p : R)) b).mp hb
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : R) (p : R)).mp c.property
  have hr : IsLeftRegular (p : S) := pDivisionFactorial_p_mul_injective (fun _ : Unit ↦ y)
  have he : (p : S) ^ n * F b = (p : S) ^ n * 0 := by
    rw [mul_zero]
    have h := congrArg F hc
    rw [← hn] at h
    simpa only [map_mul, map_pow, map_natCast, map_zero] using h
  exact (hr.pow n) he

/-- 核は正確に表示環の実p局所化の核である。 -/
theorem principalDPToFactorial_ker_eq_away_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (principalDPToFactorial hA D y) =
      RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) :=
  le_antisymm (principalDPToFactorial_ker_le_away_ker hA D y)
    (principalDPToFactorial_away_ker_le_ker hA D y)


/-- 実全射で零になることは、表示環であるp冪により消えることと同値。 -/
theorem principalDPToFactorial_eq_zero_iff
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A)
    (b : PrincipalDPPresentation A y) :
    principalDPToFactorial hA D y b = 0 ↔
      ∃ n : ℕ, (p : PrincipalDPPresentation A y) ^ n * b = 0 := by
  change b ∈ RingHom.ker (principalDPToFactorial hA D y) ↔ _
  rw [principalDPToFactorial_ker_eq_away_ker]
  change algebraMap (PrincipalDPPresentation A y)
    (Localization.Away (p : PrincipalDPPresentation A y)) b = 0 ↔ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (p : PrincipalDPPresentation A y))]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : PrincipalDPPresentation A y)
      (p : PrincipalDPPresentation A y)).mp c.property
    exact ⟨n, by simpa only [hn] using hc⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨(p : PrincipalDPPresentation A y) ^ n, ⟨n, rfl⟩⟩, hn⟩

end SerrePositivity.BhattScholze
