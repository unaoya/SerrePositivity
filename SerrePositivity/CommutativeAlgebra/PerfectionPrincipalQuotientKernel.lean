module

public import SerrePositivity.CommutativeAlgebra.PerfectionIdealCorrection
public import SerrePositivity.CommutativeAlgebra.PerfectAnnihilator

/-! # 完全標数p環の任意の主イデアル商のperfection射影核 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- aの標準p冪根。 -/
def perfectPrincipalRoot (a : k) (n : ℕ) : k :=
  ((frobeniusEquiv k p).symm : k → k)^[n] a

/-- 標準根のp^n乗は元の元。 -/
theorem perfectPrincipalRoot_pow (a : k) (n : ℕ) :
    perfectPrincipalRoot k p a n ^ p ^ n = a := by
  exact iterate_frobeniusEquiv_symm_pow_p_pow k p a n

section Quotient
variable (a : k) [CharP (k ⧸ Ideal.span {a}) p]

/-- 完全環から主イデアル商のperfectionへの標準環準同型。 -/
def principalQuotientPerfectionLift : k →+* Perfection (k ⧸ Ideal.span {a}) p :=
  Perfection.lift p k (k ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}))

/-- 標準写像の各座標。 -/
theorem principalQuotientPerfectionLift_coeff (b : k) (n : ℕ) :
    Perfection.coeff (k ⧸ Ideal.span {a}) p n (principalQuotientPerfectionLift k p a b) =
      Ideal.Quotient.mk (Ideal.span {a}) (perfectPrincipalRoot k p b n) := rfl

/-- 第0射影核の元は全座標で標準生成元により割り切れる。 -/
theorem principalQuotientPerfectionLift_coeff_dvd
    (x : Perfection (k ⧸ Ideal.span {a}) p)
    (hx : Perfection.coeff (k ⧸ Ideal.span {a}) p 0 x = 0) (n : ℕ) :
    Perfection.coeff (k ⧸ Ideal.span {a}) p n (principalQuotientPerfectionLift k p a a) ∣
      Perfection.coeff (k ⧸ Ideal.span {a}) p n x := by
  let q := Ideal.Quotient.mk (Ideal.span {a})
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff (k ⧸ Ideal.span {a}) p n x)
  have hpow : q (t ^ p ^ n) = 0 := by
    rw [map_pow, ht]
    have he := Perfection.coeffMonoidHom_pow_p_pow_self x n
    change (Perfection.coeff (k ⧸ Ideal.span {a}) p n x) ^ p ^ n =
      Perfection.coeff (k ⧸ Ideal.span {a}) p 0 x at he
    rw [he, hx]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hpow)
  have he : t = perfectPrincipalRoot k p a n * perfectPrincipalRoot k p c n := by
    apply (perfect_pow_pow_bijective k p n).1
    change t ^ p ^ n = (perfectPrincipalRoot k p a n * perfectPrincipalRoot k p c n) ^ p ^ n
    rw [mul_pow, perfectPrincipalRoot_pow, perfectPrincipalRoot_pow]
    exact hc
  rw [principalQuotientPerfectionLift_coeff, ← ht, he, map_mul]
  exact dvd_mul_right _ _

/-- 任意の零因子も含む、主イデアル商のperfectionの第0射影核の生成公式。 -/
theorem perfection_principal_quotient_coeff_zero_kernel_eq_span :
    RingHom.ker (Perfection.coeff (k ⧸ Ideal.span {a}) p 0) =
      Ideal.span {principalQuotientPerfectionLift k p a a} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply perfection_dvd_of_coeff_dvd_of_ideal_correction (k ⧸ Ideal.span {a}) p
      (principalQuotientPerfectionLift k p a a) x (quotientAnnihilatorImage k a)
    · exact quotientAnnihilatorImage_has_p_roots k p a
    · intro n z hz
      rw [principalQuotientPerfectionLift_coeff]
      exact quotientAnnihilatorImage_killed_by_p_root k p a _ n
        (perfectPrincipalRoot_pow k p a n) z hz
    · exact principalQuotientPerfectionLift_coeff_dvd k p a x hx
    · intro n z hz
      rw [principalQuotientPerfectionLift_coeff] at hz
      exact quotient_p_root_annihilator_pow_mem k p a _ n
        (perfectPrincipalRoot_pow k p a (n + 1)) z hz
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change Perfection.coeff (k ⧸ Ideal.span {a}) p 0 (principalQuotientPerfectionLift k p a a) = 0
    rw [principalQuotientPerfectionLift_coeff]
    change Ideal.Quotient.mk (Ideal.span {a}) a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)

/-- BS要求の標準Perfection.liftをそのまま使う公開署名。 -/
theorem perfection_lift_principal_quotient_kernel :
    RingHom.ker (Perfection.coeff (k ⧸ Ideal.span {a}) p 0) =
      Ideal.span {((Perfection.lift p k (k ⧸ Ideal.span {a}))
        (Ideal.Quotient.mk (Ideal.span {a}))) a} :=
  perfection_principal_quotient_coeff_zero_kernel_eq_span k p a

end Quotient

omit [CharP k p] [Fact p.Prime] in
/-- 零環の商の枝は元の互換列とモノイド持上げで扱う。CharP Q pを要求しない。 -/
theorem perfection_principal_quotient_zero_branch (a : k)
    [Subsingleton (k ⧸ Ideal.span {a})] (x : Perfection (k ⧸ Ideal.span {a}) p) :
    Perfection.coeffMonoidHom (k ⧸ Ideal.span {a}) p 0 x = 0 ↔
      ∃ b : Perfection (k ⧸ Ideal.span {a}) p,
        x = Perfection.liftMonoidHom p k (k ⧸ Ideal.span {a})
          (Ideal.Quotient.mk (Ideal.span {a})).toMonoidHom a * b := by
  constructor
  · intro _
    refine ⟨x, ?_⟩
    apply Perfection.extMonoid
    intro n
    exact Subsingleton.elim _ _
  · intro _
    exact Subsingleton.elim _ _

end SerrePositivity
