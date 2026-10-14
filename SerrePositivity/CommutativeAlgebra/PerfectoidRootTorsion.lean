module

public import SerrePositivity.CommutativeAlgebra.PerfectoidPTorsion

/-! # pの根によるperfectoid環のpねじれの零化

p=unit·π^N（N>1）なら、pで消える元はπで消える。
πの正則性やperfectoid環全体の被約性を仮定せず、tiltの被約性とWitt環でのpの
キャンセルを使う。p冪ねじれについては、既存のpによる零化と合わせる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- pねじれは、pの任意の正の冪根（指数N>1）で消える。 -/
theorem IsIntegralPerfectoid.root_mul_eq_zero_of_p_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (N : ℕ) (hN : 1 < N) (hpEq : (p : S) = u * π ^ N)
    (x : S) (hx : (p : S) * x = 0) : π * x = 0 := by
  rcases hS with hsub | ⟨hp, hc, _, hF, hker⟩
  · let : Subsingleton S := hsub
    exact Subsingleton.elim _ _
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, hq⟩ := exists_untilt_unit_mul_of_power S p hF π u N hN hpEq
    let w : Sˣ := u * (v⁻¹) ^ N
    have hpq : (p : S) = (w : S) * q.untilt ^ N := by
      rw [hq, mul_pow, hpEq]
      change (u : S) * π ^ N =
        ((u : S) * (↑(v⁻¹) : S) ^ N) * ((v : S) ^ N * π ^ N)
      calc
        _ = (u : S) * (((↑(v⁻¹) : S) * (v : S)) ^ N * π ^ N) := by simp
        _ = _ := by simp only [mul_pow]; ring
    obtain ⟨a, ha⟩ := surjective_fontaineTheta hF (-(w : S))
    have ha0 : IsUnit (a.coeff 0) := by
      apply perfection_isUnit_of_coeff_zero (ModP S p) p
      change IsUnit (PreTilt.coeff 0 (a.coeff 0))
      rw [← WittVector.mk_fontaineTheta, ha]
      exact (w.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : S)}))
    let ξ := (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ N * a
    have hξ : ξ ∈ RingHom.ker (WittVector.fontaineTheta S p) := by
      change WittVector.fontaineTheta S p ξ = 0
      dsimp only [ξ]
      rw [map_add, map_natCast, map_mul, map_pow, WittVector.fontaineTheta_teichmuller, ha]
      rw [hpq]
      ring
    have hqzero : (PreTilt.coeff 0 q) ^ N = 0 := by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, ← map_pow]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : (w : S) * q.untilt ^ N ∈ Ideal.span {(p : S)} := by
        rw [← hpq]
        exact Ideal.subset_span (Set.mem_singleton _)
      simpa [mul_assoc] using
        (Ideal.span {(p : S)}).mul_mem_left (↑(w⁻¹) : S) hm
    have hgen : RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {ξ} := by
      apply ker_fontaineTheta_eq_span_of_firstCoeff_unit S p hker ξ hξ
      change IsUnit (PreTilt.coeff 0
        (((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ N * a).coeff 1))
      rw [primitive_shape_firstCoeff_eq_one_of_power S p q a N hqzero]
      exact isUnit_one
    let : IsReduced (PreTilt S p) := isReduced_of_perfectRing_charP (PreTilt S p) p
    obtain ⟨b, hb⟩ := surjective_fontaineTheta hF x
    have hdiv : ξ ∣ (p : WittVector p (PreTilt S p)) * b := by
      apply Ideal.mem_span_singleton.mp
      rw [← hgen]
      change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) * b) = 0
      simpa only [map_mul, map_natCast, hb] using hx
    have hd := witt_teichmuller_mul_dvd_of_p_mul_dvd (PreTilt S p) p q a b N
      (Nat.zero_lt_of_lt hN) ha0 hdiv
    have hm : WittVector.teichmuller p q * b ∈ RingHom.ker (WittVector.fontaineTheta S p) := by
      rw [hgen]
      exact Ideal.mem_span_singleton.mpr hd
    change WittVector.fontaineTheta S p (WittVector.teichmuller p q * b) = 0 at hm
    rw [map_mul, WittVector.fontaineTheta_teichmuller, hb, hq] at hm
    apply v.isUnit.mul_right_eq_zero.mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

/-- p冪ねじれをpで零化してから、pの根による零化へ移す。 -/
theorem IsIntegralPerfectoid.root_mul_eq_zero_of_pow_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (N : ℕ) (hN : 1 < N) (hpEq : (p : S) = u * π ^ N)
    (n : ℕ) (x : S) (hx : (p : S) ^ n * x = 0) : π * x = 0 :=
  hS.root_mul_eq_zero_of_p_mul_eq_zero S p π u N hN hpEq x
    (hS.p_mul_eq_zero_of_pow_mul_eq_zero S p n x hx)

/-- p^n乗根は、任意のp冪ねじれ元を消す。n=0もpによる零化として含める。 -/
theorem IsIntegralPerfectoid.p_power_root_mul_eq_zero_of_pow_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (ρ : S) (n : ℕ) (hρ : ρ ^ (p ^ n) = (p : S))
    (m : ℕ) (x : S) (hx : (p : S) ^ m * x = 0) : ρ * x = 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, pow_one] at hρ
    rw [hρ]
    exact hS.p_mul_eq_zero_of_pow_mul_eq_zero S p m x hx
  · exact hS.root_mul_eq_zero_of_pow_mul_eq_zero S p ρ 1 (p ^ n)
      (one_lt_pow₀ (Fact.out : p.Prime).one_lt hn)
      (by simpa only [Units.val_one, one_mul] using hρ.symm) m x hx

/-- pの正冪根の倍数がpねじれなら、その倍数は零。
根の主イデアルとpねじれの交わりを、p冪ねじれの有界性で制御する。 -/
theorem IsIntegralPerfectoid.root_mul_eq_zero_of_p_mul_root_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (N : ℕ) (hN : 1 < N) (hpEq : (p : S) = u * π ^ N)
    (x : S) (hx : (p : S) * (π * x) = 0) : π * x = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hN))
  have hp2 : (p : S) ^ 2 * x = 0 := by
    calc
      _ = (u : S) * π ^ n * ((p : S) * (π * x)) := by
        nth_rw 1 [pow_two, hpEq]
        rw [hn, pow_succ]
        ring
      _ = 0 := by rw [hx]; simp
  exact hS.root_mul_eq_zero_of_pow_mul_eq_zero S p π u N hN hpEq 2 x hp2

/-- pねじれ元のp乗がpで割れるなら、その元は零。
全環の被約性を仮定せず、Frobenius核と根の主イデアルの交わりから導く。 -/
theorem IsIntegralPerfectoid.eq_zero_of_p_mul_eq_zero_of_pow_mem_p
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x : S) (hx : (p : S) * x = 0) (hxp : x ^ p ∈ Ideal.span {(p : S)}) : x = 0 := by
  rcases hS with hsub | ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
  · exact hsub.elim _ _
  · have hS : IsIntegralPerfectoid S p := Or.inr ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
    have hm : x ∈ Ideal.span {π} :=
      hS.frobenius_kernel_of_unit_root S p π u hpEq x (by
        rwa [hpEq, Ideal.span_singleton_mul_left_unit u.isUnit] at hxp)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
    rw [hy] at hx ⊢
    exact hS.root_mul_eq_zero_of_p_mul_root_mul_eq_zero S p π u p
      (Fact.out : p.Prime).one_lt hpEq y hx

/-- pねじれ元に対するFrobeniusの核は零。 -/
theorem IsIntegralPerfectoid.eq_zero_of_p_mul_eq_zero_of_pow_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x : S) (hx : (p : S) * x = 0) (hxp : x ^ p = 0) : x = 0 :=
  hS.eq_zero_of_p_mul_eq_zero_of_pow_mem_p S p x hx (hxp ▸ Ideal.zero_mem _)

/-- pねじれ元に対するp乗写像は単射。mod pで差のp乗を計算する。 -/
theorem IsIntegralPerfectoid.pow_injective_on_p_torsion
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x y : S) (hx : (p : S) * x = 0) (hy : (p : S) * y = 0)
    (hxy : x ^ p = y ^ p) : x = y := by
  rcases hS with hsub | hdata
  · exact hsub.elim _ _
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨hp, _, _⟩ := hdata
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  apply sub_eq_zero.mp
  apply hS.eq_zero_of_p_mul_eq_zero_of_pow_mem_p S p (x - y)
    (by rw [mul_sub, hx, hy, sub_self])
  let q := Ideal.Quotient.mk (Ideal.span {(p : S)})
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q ((x - y) ^ p) = 0
  rw [map_pow, map_sub, sub_pow_char, ← map_pow, ← map_pow, hxy, sub_self]

end SerrePositivity
