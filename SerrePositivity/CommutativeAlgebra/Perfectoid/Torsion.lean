module

public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.Nilpotent.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.SMul
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Perfection
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid

/-! # 整 perfectoid 環の p ねじれ

## 概要

整 perfectoid 環の p 冪ねじれは p で消え（`p_mul_eq_zero_of_pow_mul_eq_zero`）、p = 単元·π^N（N > 1）なら p ねじれは π で消える。p ねじれの元は p 乗根を持ち、その根も p ねじれである。p ねじれのイデアル `pTorsionIdeal` による商は p 進完備で p が非零因子、Frobenius 核の条件と tilt の第 0 射影の核が商へ移り、商も整 perfectoid になる（`pTorsionQuotient_isIntegralPerfectoid`）。正則な p 乗根と Frobenius 核の条件から被約性を導き、整 perfectoid 環は被約である（`IsIntegralPerfectoid.isReduced`）。環準同型と untilt は両立する（`untilt_map`）。

## 方針

Fontaine 核の distinguished な生成元と、完全被約な係数の Witt 環での p の打ち消しを使う。商への移送は、p ねじれの p 乗根を選んで誤差を除き、元の環の Frobenius 核の条件を適用する。

## 規約

`IsIntegralPerfectoid.isReduced`・`modPMap`・`untilt_map`・`pTorsionIdeal` は BhattScholze・CLMST が名前で参照する。perfectoid イデアルとの比較（`perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid`）は BhattScholze に依存するので PerfectoidIdealPowers に置く。p ねじれ商への mod p の写像は `modPMap` を使う。

## 使われ方

BhattScholze の perfectoid 化と almost 数学、CLMST の巡回ねじれの比較、`RootTower/Perfectoid`。
-/

@[expose] public noncomputable section

universe u

section WittDistinguishedTorsionPart

namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    [PerfectRing R p] [IsReduced R]

omit [PerfectRing R p] in
/-- 第1係数が単元の関係式と、二つの零係数を持つ積から、因子の第0係数は零。 -/
theorem witt_factor_coeff_zero_of_distinguished (ξ a : WittVector p R)
    (hξ : IsUnit (ξ.coeff 1)) (h0 : (ξ * a).coeff 0 = 0) (h1 : (ξ * a).coeff 1 = 0) :
    a.coeff 0 = 0 := by
  have hz : ξ.coeff 0 * a.coeff 0 = 0 := by
    simpa only [WittVector.mul_coeff_zero] using h0
  have hf : ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p = 0 := by
    simpa only [witt_mul_coeff_one, CharP.cast_eq_zero, zero_mul, add_zero] using h1
  have hn : (a.coeff 0) ^ (p + p) = 0 := by
    apply hξ.mul_right_eq_zero.mp
    calc
      _ = (ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p) * a.coeff 0 ^ p -
          a.coeff 1 * (ξ.coeff 0 * a.coeff 0) ^ p := by
        rw [pow_add, mul_pow]
        ring
      _ = 0 := by rw [hf, hz, zero_pow (Fact.out : p.Prime).ne_zero]; simp
  exact IsReduced.eq_zero _ ⟨p + p, hn⟩

/-- distinguished関係式によるWitt商のp冪ねじれはpで消える。 -/
theorem witt_distinguished_dvd_p_mul_of_dvd_p_pow_mul (ξ b : WittVector p R)
    (hξ : IsUnit (ξ.coeff 1)) (n : ℕ) (hn : 0 < n)
    (hdiv : ξ ∣ (p : WittVector p R) ^ n * b) : ξ ∣ (p : WittVector p R) * b := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [zero_add, pow_one] using hdiv
    · obtain ⟨a, ha⟩ := hdiv
      have h0 : (ξ * a).coeff 0 = 0 := by
        rw [← ha, mul_comm]
        exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp
          (Ideal.mem_span_singleton.mpr ⟨b, mul_comm _ _⟩) 0 (by omega)
      have h1 : (ξ * a).coeff 1 = 0 := by
        rw [← ha, mul_comm]
        exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp
          (Ideal.mem_span_singleton.mpr ⟨b, mul_comm _ _⟩) 1 (by omega)
      have ha0 := witt_factor_coeff_zero_of_distinguished R p ξ a hξ h0 h1
      obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr ha0)
      have heq : (p : WittVector p R) * (ξ * a') =
          (p : WittVector p R) * ((p : WittVector p R) ^ n * b) := by
        calc
          _ = ξ * a := by rw [ha']; ac_rfl
          _ = _ := by rw [← ha, pow_succ]; ac_rfl
      have hcancel : ξ * a' = (p : WittVector p R) ^ n * b := by
        apply sub_eq_zero.mp
        apply WittVector.eq_zero_of_p_mul_eq_zero
        rw [mul_comm, mul_sub, heq, sub_self]
      exact ih (Nat.pos_of_ne_zero hn0) ⟨a', hcancel.symm⟩

omit [PerfectRing R p] in
/-- p b=(p+[q]^N a)dという関係式では、qがdの第0係数を消す。 -/
theorem witt_relation_factor_coeff_zero_annihilated (q : R) (a b d : WittVector p R)
    (N : ℕ) (hN : 0 < N) (ha : IsUnit (a.coeff 0))
    (hd : (p : WittVector p R) * b =
      ((p : WittVector p R) + WittVector.teichmuller p q ^ N * a) * d) :
    q * d.coeff 0 = 0 := by
  let ξ := (p : WittVector p R) + WittVector.teichmuller p q ^ N * a
  have hco : q ^ N * d.coeff 0 = 0 := by
    have hh := congrArg (WittVector.constantCoeff : WittVector p R →+* R) hd
    change _ = WittVector.constantCoeff (ξ * d) at hh
    simp only [ξ, map_mul, map_add, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul,
      zero_add, WittVector.constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, WittVector.teichmuller_coeff_zero] at hh
    apply ha.mul_right_eq_zero.mp
    calc
      _ = (q ^ N * a.coeff 0) * d.coeff 0 := by ac_rfl
      _ = 0 := hh.symm
  apply IsReduced.eq_zero
  refine ⟨N, ?_⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [hn] at hco ⊢
  calc
    _ = (q ^ (n + 1) * d.coeff 0) * d.coeff 0 ^ n := by
      rw [mul_pow, pow_succ (d.coeff 0)]
      ac_rfl
    _ = 0 := by rw [hco, zero_mul]

/-- p+[q]^N aという関係式でaの第0係数が単元なら、pねじれは[q]で消える。 -/
theorem witt_teichmuller_mul_dvd_of_p_mul_dvd (q : R) (a b : WittVector p R)
    (N : ℕ) (hN : 0 < N) (ha : IsUnit (a.coeff 0))
    (hdiv : (p : WittVector p R) + WittVector.teichmuller p q ^ N * a ∣
      (p : WittVector p R) * b) :
    (p : WittVector p R) + WittVector.teichmuller p q ^ N * a ∣
      WittVector.teichmuller p q * b := by
  let ξ := (p : WittVector p R) + WittVector.teichmuller p q ^ N * a
  obtain ⟨d, hd⟩ := hdiv
  have hqd := witt_relation_factor_coeff_zero_annihilated R p q a b d N hN ha hd
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero (WittVector.teichmuller p q * d)).mpr
      (by simpa only [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] using hqd))
  have heq : (p : WittVector p R) * (WittVector.teichmuller p q * b) =
      (p : WittVector p R) * (ξ * v) := by
    calc
      _ = WittVector.teichmuller p q * ((p : WittVector p R) * b) := by ac_rfl
      _ = ξ * (WittVector.teichmuller p q * d) := by rw [hd]; dsimp only [ξ]; ac_rfl
      _ = _ := by rw [hv]; ac_rfl
  have hcancel : WittVector.teichmuller p q * b = ξ * v := by
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    rw [mul_comm, mul_sub, heq, sub_self]
  exact ⟨v, hcancel⟩

/-- 関係式による商のpねじれには、qで消える元のTeichmuller代表がある。 -/
theorem witt_exists_teichmuller_representative_of_p_mul_dvd
    (q : R) (a b : WittVector p R) (N : ℕ) (hN : 0 < N) (ha : IsUnit (a.coeff 0))
    (hdiv : (p : WittVector p R) + WittVector.teichmuller p q ^ N * a ∣
      (p : WittVector p R) * b) :
    ∃ r : R, q * r = 0 ∧
      ((p : WittVector p R) + WittVector.teichmuller p q ^ N * a) ∣
        b - WittVector.teichmuller p r := by
  let ξ := (p : WittVector p R) + WittVector.teichmuller p q ^ N * a
  obtain ⟨d, hd⟩ := hdiv
  have hqd := witt_relation_factor_coeff_zero_annihilated R p q a b d N hN ha hd
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero
      (d - WittVector.teichmuller p (d.coeff 0))).mpr (by
        change (WittVector.constantCoeff : WittVector p R →+* R)
          (d - WittVector.teichmuller p (d.coeff 0)) = 0
        rw [map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
          WittVector.teichmuller_coeff_zero, sub_self]))
  have hqteich : WittVector.teichmuller p q * WittVector.teichmuller p (d.coeff 0) = 0 := by
    rw [← map_mul, hqd, WittVector.teichmuller_zero]
  have hξteich : ξ * WittVector.teichmuller p (d.coeff 0) =
      (p : WittVector p R) * WittVector.teichmuller p (d.coeff 0) := by
    dsimp only [ξ]
    rw [add_mul]
    have hz : WittVector.teichmuller p q ^ N * WittVector.teichmuller p (d.coeff 0) = 0 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      rw [pow_succ, mul_assoc, hqteich, mul_zero]
    rw [mul_right_comm _ a, hz, zero_mul, add_zero]
  have hcancel : b - WittVector.teichmuller p (d.coeff 0) = ξ * e := by
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    rw [mul_comm, mul_sub, mul_sub, hd, ← hξteich, ← mul_sub, he]
    ring
  exact ⟨d.coeff 0, hqd, e, hcancel⟩

end SerrePositivity

end WittDistinguishedTorsionPart

section PerfectoidPTorsionPart

namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- 整perfectoid環のp冪ねじれはpで消える。四条件から証明し、外部引用を加えない。 -/
theorem IsIntegralPerfectoid.p_mul_eq_zero_of_pow_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (n : ℕ) (x : S) (hx : (p : S) ^ n * x = 0) : (p : S) * x = 0 := by
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, one_mul, mul_zero] using congrArg (fun y ↦ (p : S) * y) hx
  rcases hS with hsub | ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
  · let : Subsingleton S := hsub
    exact Subsingleton.elim _ _
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, a, hq, hgen⟩ :=
      exists_untilt_unit_mul_and_kernel_generator S p hF hker π u hpEq
    let ξ : WittVector p (PreTilt S p) := (p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a
    have hπ : π ^ p ∈ Ideal.span {(p : S)} := by
      have hh : (u : S) * π ^ p ∈ Ideal.span {(p : S)} := by
        rw [← hpEq]
        exact Ideal.subset_span (Set.mem_singleton _)
      simpa [mul_assoc] using (Ideal.span {(p : S)}).mul_mem_left (↑(u⁻¹) : S) hh
    have hqpow : q.untilt ^ p ∈ Ideal.span {(p : S)} := by
      rw [hq, mul_pow]
      exact (Ideal.span {(p : S)}).mul_mem_left _ hπ
    have hfirst : IsUnit (ξ.coeff 1) := by
      apply perfection_isUnit_of_coeff_zero (ModP S p) p
      change IsUnit (PreTilt.coeff 0 (ξ.coeff 1))
      rw [primitive_shape_firstCoeff_eq_one S p q a
        (coeff_zero_pow_eq_zero_of_untilt_pow_mem_p S p q hqpow)]
      exact isUnit_one
    let : IsReduced (PreTilt S p) :=
      isReduced_of_perfectPower (PreTilt S p) p (Fact.out : p.Prime).one_lt
    obtain ⟨w, hw⟩ := surjective_fontaineTheta hF x
    have hdiv : ξ ∣ (p : WittVector p (PreTilt S p)) ^ n * w := by
      apply Ideal.mem_span_singleton.mp
      rw [← hgen]
      change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) ^ n * w) = 0
      simpa only [map_mul, map_pow, map_natCast, hw] using hx
    have hd := witt_distinguished_dvd_p_mul_of_dvd_p_pow_mul (PreTilt S p) p ξ w
      hfirst n (Nat.pos_of_ne_zero hn) hdiv
    have hm : (p : WittVector p (PreTilt S p)) * w ∈
        RingHom.ker (WittVector.fontaineTheta S p) := by
      rw [hgen]
      exact Ideal.mem_span_singleton.mpr hd
    change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) * w) = 0 at hm
    simpa only [map_mul, map_natCast, hw] using hm

/-- pが冪零の整perfectoid環ではp=0。 -/
theorem IsIntegralPerfectoid.p_eq_zero_of_isNilpotent
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (hp : IsNilpotent (p : S)) : (p : S) = 0 := by
  obtain ⟨n, hn⟩ := hp
  simpa only [mul_one] using hS.p_mul_eq_zero_of_pow_mul_eq_zero S p n 1
    (by simpa only [mul_one] using hn)

end SerrePositivity

end PerfectoidPTorsionPart

section PerfectoidRootTorsionPart

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
    let : IsReduced (PreTilt S p) :=
      isReduced_of_perfectPower (PreTilt S p) p (Fact.out : p.Prime).one_lt
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

/-- pねじれ元が冪零なら零。p冪乗による零化を反復して降ろす。 -/
theorem IsIntegralPerfectoid.eq_zero_of_p_mul_eq_zero_of_isNilpotent
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x : S) (hx : (p : S) * x = 0) (hn : IsNilpotent x) : x = 0 := by
  have hdesc : ∀ n : ℕ, x ^ (p ^ n) = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
        intro h
        simpa only [pow_zero, pow_one] using h
    | succ n ih =>
        intro hpow
        have hpt : (p : S) * x ^ (p ^ n) = 0 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (pow_pos (Fact.out : p.Prime).pos n))
          rw [hk, pow_succ, mul_left_comm, hx, mul_zero]
        apply ih
        apply hS.eq_zero_of_p_mul_eq_zero_of_pow_eq_zero S p _ hpt
        simpa only [pow_succ, pow_mul] using hpow
  obtain ⟨n, hn⟩ := hn
  apply hdesc n
  have hnp : n < 2 ^ n := Nat.lt_two_pow_self
  exact pow_eq_zero_of_le
    (hnp.le.trans (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le n)) hn

end SerrePositivity

end PerfectoidRootTorsionPart

section PerfectoidTorsionRootsPart

namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- pねじれ元にはpねじれのp乗根が存在する。外部の構造定理を引用しない。 -/
theorem IsIntegralPerfectoid.exists_p_torsion_p_root
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x : S) (hx : (p : S) * x = 0) : ∃ y : S, (p : S) * y = 0 ∧ y ^ p = x := by
  rcases hS with hsub | ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
  · exact ⟨0, mul_zero _, hsub.elim _ _⟩
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, a, hq, ha0, hgen⟩ :=
      exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hpEq
    let : IsReduced (PreTilt S p) :=
      isReduced_of_perfectPower (PreTilt S p) p (Fact.out : p.Prime).one_lt
    obtain ⟨b, hb⟩ := surjective_fontaineTheta hF x
    have hdiv : (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a ∣
        (p : WittVector p (PreTilt S p)) * b := by
      apply Ideal.mem_span_singleton.mp
      rw [← hgen]
      change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) * b) = 0
      simpa only [map_mul, map_natCast, hb] using hx
    obtain ⟨r, hqr, hr⟩ := witt_exists_teichmuller_representative_of_p_mul_dvd
      (PreTilt S p) p q a b p (Fact.out : p.Prime).pos ha0 hdiv
    have hrx : r.untilt = x := by
      have hm : b - WittVector.teichmuller p r ∈ RingHom.ker (WittVector.fontaineTheta S p) := by
        rw [hgen]
        exact Ideal.mem_span_singleton.mpr hr
      change WittVector.fontaineTheta S p (b - WittVector.teichmuller p r) = 0 at hm
      rw [map_sub, hb, WittVector.fontaineTheta_teichmuller] at hm
      exact (sub_eq_zero.mp hm).symm
    let t := (frobeniusEquiv (PreTilt S p) p).symm r
    have ht : t ^ p = r := frobeniusEquiv_symm_pow_p (PreTilt S p) p r
    have hqt : q * t = 0 := by
      apply IsReduced.eq_zero
      refine ⟨p, ?_⟩
      rw [mul_pow, ht]
      have hqp : q ^ p = q ^ (p - 1) * q := by
        simpa only [Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using pow_succ q (p - 1)
      rw [hqp, mul_assoc, hqr, mul_zero]
    have hπt : π * t.untilt = 0 := by
      have hh := congrArg (PreTilt.untilt : PreTilt S p →* S) hqt
      have hz : (0 : PreTilt S p).untilt = 0 := by
        rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
      rw [map_mul, hz, hq, mul_assoc] at hh
      exact v.isUnit.mul_right_eq_zero.mp hh
    refine ⟨t.untilt, ?_, ?_⟩
    · rw [hpEq]
      have hπp : π ^ p = π ^ (p - 1) * π := by
        simpa only [Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using pow_succ π (p - 1)
      rw [hπp, mul_assoc, mul_assoc, hπt, mul_zero, mul_zero]
    · rw [← map_pow, ht, hrx]

end SerrePositivity

end PerfectoidTorsionRootsPart

section PerfectoidReducedPart

namespace SerrePositivity

/-- 正則な p 乗根と具体的な Frobenius 核条件、p 進分離性から環は reduced。
x^p=0 の場合を正則 π で繰り返し割り、p の全冪に入ることを示す。
p ねじれを許す perfectoid 環の一般の reduced 定理とは区別する。 -/
theorem isReduced_of_regular_unit_root_frobenius_kernel
    (R : Type u) [CommRing R] (p : ℕ) (hp : 1 < p)
    (π : R) (u : Rˣ) (hπ : (p : R) = u * π ^ p) (hregular : IsSMulRegular R π)
    (hsep : IsHausdorff (Ideal.span {(p : R)}) R)
    (hF : ∀ x : R, x ^ p ∈ Ideal.span {(p : R)} → x ∈ Ideal.span {π}) :
    IsReduced R := by
  apply (isReduced_iff_pow_one_lt p hp).mpr
  intro x hx
  have hfactor (k : ℕ) : ∃ y : R, x = π ^ k * y ∧ y ^ p = 0 := by
    induction k with
    | zero => exact ⟨x, by simp, hx⟩
    | succ k ih =>
        obtain ⟨y, hxy, hy⟩ := ih
        have hyπ : y ∈ Ideal.span {π} := hF y (hy ▸ Ideal.zero_mem _)
        obtain ⟨z, hyz⟩ := Ideal.mem_span_singleton.mp hyπ
        have hz : z ^ p = 0 := by
          apply IsSMulRegular.pow p hregular
          change π ^ p * z ^ p = π ^ p * 0
          rw [← mul_pow, ← hyz, hy, mul_zero]
        refine ⟨z, ?_, hz⟩
        rw [hxy, hyz, pow_succ, mul_assoc]
  apply hsep.haus x
  intro n
  apply SModEq.zero.mpr
  change x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Ideal R)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨y, hxy, _⟩ := hfactor (p * n)
  apply Ideal.mem_span_singleton.mpr
  have hπp : π ^ p = (↑(u⁻¹) : R) * (p : R) := by
    rw [hπ]
    simp
  refine ⟨(↑(u⁻¹) : R) ^ n * y, ?_⟩
  simpa only [pow_mul, hπp, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hxy

end SerrePositivity

end PerfectoidReducedPart

section PerfectoidTorsionQuotientPart

namespace SerrePositivity

/-- pで消える元のイデアル。 -/
def pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) : Ideal S where
  carrier := {x | (p : S) * x = 0}
  zero_mem' := mul_zero _
  add_mem' := by
    intro a b ha hb
    change (p : S) * a = 0 at ha
    change (p : S) * b = 0 at hb
    change (p : S) * (a + b) = 0
    rw [mul_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change (p : S) * b = 0 at hb
    change (p : S) * (a * b) = 0
    rw [mul_left_comm, hb, mul_zero]

@[simp] theorem mem_pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) (x : S) :
    x ∈ pTorsionIdeal S p ↔ (p : S) * x = 0 := Iff.rfl

/-- p進完備な環のpねじれ商はp進完備。perfectoid性やNoether性は不要。 -/
theorem pTorsionQuotient_isAdicComplete
    (S : Type u) [CommRing S] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
      (S ⧸ pTorsionIdeal S p) := by
  have hker : pTorsionIdeal S p = LinearMap.ker (LinearMap.mulLeft S (p : S)) := rfl
  let : IsAdicComplete (Ideal.span {(p : S)}) (S ⧸ pTorsionIdeal S p) := by
    rw [hker]
    exact isAdicComplete_quotient_ker (Ideal.span {(p : S)})
      (LinearMap.mulLeft S (p : S))
  have hmap : (Ideal.span {(p : S)}).map
      (algebraMap S (S ⧸ pTorsionIdeal S p)) =
      Ideal.span {(p : S ⧸ pTorsionIdeal S p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

/-- perfectoid環のpねじれ商の完備性。零環の場合も含む。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isAdicComplete
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsAdicComplete (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
      (S ⧸ pTorsionIdeal S p) := by
  rcases hS with hsub | ⟨_, hc, _⟩
  · let : Subsingleton S := hsub
    infer_instance
  · let := hc
    exact SerrePositivity.pTorsionQuotient_isAdicComplete S p

/-- perfectoid環のpねじれを除いた商では、pは非零因子として作用する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_p_mul_injective
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    Function.Injective (fun x : S ⧸ pTorsionIdeal S p ↦ (p : S ⧸ pTorsionIdeal S p) * x) := by
  have hzero (x : S ⧸ pTorsionIdeal S p) (hx : (p : S ⧸ pTorsionIdeal S p) * x = 0) :
      x = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (p : S) * ((p : S) * x) = 0 := by
      apply (mem_pTorsionIdeal S p _).mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, map_natCast]
      exact hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hS.p_mul_eq_zero_of_pow_mul_eq_zero S p 2 x
      (by simpa only [pow_two, mul_assoc] using hx')
  intro x y hxy
  dsimp only at hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [mul_sub, hxy, sub_self]

/-- pねじれ商では、p=unit·π^Nの任意の正冪根も非零因子。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_root_mul_injective
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S ⧸ pTorsionIdeal S p) (u : (S ⧸ pTorsionIdeal S p)ˣ)
    (N : ℕ) (hN : 0 < N) (hπ : (p : S ⧸ pTorsionIdeal S p) = u * π ^ N) :
    Function.Injective (fun x : S ⧸ pTorsionIdeal S p ↦ π * x) := by
  intro x y hxy
  change π * x = π * y at hxy
  apply hS.pTorsionQuotient_p_mul_injective S p
  dsimp only
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [hπ, pow_succ, mul_assoc, hxy]

/-- 任意の商でもmod pのFrobeniusの全射性は引き継がれる。完備性やFontaine核は別途必要。 -/
theorem IsIntegralPerfectoid.surjective_pow_mod_p_quotient
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (I : Ideal S) :
    Function.Surjective (fun x : (S ⧸ I) ⧸ Ideal.span {(p : S ⧸ I)} ↦ x ^ p) := by
  rcases hS with hsub | ⟨_, _, _, hF, _⟩
  · let : Subsingleton S := hsub
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · let q := Ideal.Quotient.mk I
    have hmap : Ideal.span {(p : S)} ≤ (Ideal.span {(p : S ⧸ I)}).comap q := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)
    let f := Ideal.quotientMap (Ideal.span {(p : S ⧸ I)}) q hmap
    have hf : Function.Surjective f := Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective
    intro x
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨z, hz⟩ := hF y
    refine ⟨f z, ?_⟩
    change (f z) ^ p = x
    change z ^ p = y at hz
    rw [← map_pow, hz, hy]

end SerrePositivity

end PerfectoidTorsionQuotientPart

section PerfectoidTorsionFrobeniusPart

namespace SerrePositivity

/-- pねじれ商のFrobenius核は、元のp乗根の像で生成される。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_frobenius_kernel
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (hπ : (p : S) = u * π ^ p)
    (x : S ⧸ pTorsionIdeal S p)
    (hx : x ^ p ∈ Ideal.span {(p : S ⧸ pTorsionIdeal S p)}) :
    x ∈ Ideal.span {Ideal.Quotient.mk (pTorsionIdeal S p) π} := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    rw [Subsingleton.elim x 0]
    exact Ideal.zero_mem _
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨hp, _, _⟩ := hdata
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ht : (p : S) * (x ^ p - (p : S) * b) = 0 := by
    apply (mem_pTorsionIdeal S p _).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x ^ p - (p : S) * b) = 0
    rw [map_sub, map_pow, map_mul, map_natCast]
    exact sub_eq_zero.mpr hb
  obtain ⟨y, hy, hyp⟩ := hS.exists_p_torsion_p_root S p _ ht
  have hdiff : (x - y) ^ p ∈ Ideal.span {(p : S)} := by
    let k := Ideal.Quotient.mk (Ideal.span {(p : S)})
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change k ((x - y) ^ p) = 0
    rw [map_pow, map_sub, sub_pow_char, ← map_pow, ← map_pow, hyp,
      map_sub, map_mul, map_natCast]
    have hkp : k (p : S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [show (p : S ⧸ Ideal.span {(p : S)} ) = 0 from by
      simpa only [map_natCast] using hkp, zero_mul, sub_zero, sub_self]
  have hm : x - y ∈ Ideal.span {π} :=
    hS.frobenius_kernel_of_unit_root S p π u hπ _ (by
      rwa [hπ, Ideal.span_singleton_mul_left_unit u.isUnit] at hdiff)
  have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hm' := Ideal.mem_map_of_mem q hm
  simpa only [Ideal.map_span, Set.image_singleton, map_sub, hqy, sub_zero] using hm'

/-- pねじれ商は被約。Fontaine核の単項性や商のperfectoid性を仮定しない。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isReduced
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsReduced (S ⧸ pTorsionIdeal S p) := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨_, _, ⟨π, u, hπ⟩, _⟩ := hdata
  let Q := S ⧸ pTorsionIdeal S p
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  let v : Qˣ := Units.map q.toMonoidHom u
  have hqπ : (p : Q) = v * (q π) ^ p := by
    change (p : Q) = q (u : S) * (q π) ^ p
    simpa only [map_mul, map_pow, map_natCast] using congrArg q hπ
  let := hS.pTorsionQuotient_isAdicComplete S p
  apply isReduced_of_regular_unit_root_frobenius_kernel Q p (Fact.out : p.Prime).one_lt
    (q π) v hqπ (hS.pTorsionQuotient_root_mul_injective S p (q π) v p
      (Fact.out : p.Prime).pos hqπ) inferInstance
  exact hS.pTorsionQuotient_frobenius_kernel S p π u hπ

/-- 整perfectoid環は被約。ねじれ商の被約性から冪零元をpねじれへ帰着する。 -/
theorem IsIntegralPerfectoid.isReduced
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsReduced S := by
  let := hS.pTorsionQuotient_isReduced S p
  refine ⟨fun x hx ↦ ?_⟩
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  have hq : q x = 0 := IsReduced.eq_zero _ (hx.map q)
  exact hS.eq_zero_of_p_mul_eq_zero_of_isNilpotent S p x
    (Ideal.Quotient.eq_zero_iff_mem.mp hq) hx

end SerrePositivity

end PerfectoidTorsionFrobeniusPart

section PerfectoidUntiltNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime]

def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap (Ideal.span {(p : S)}) f (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _))

omit [Fact p.Prime] in
/-- 全射な環準同型は mod p でも全射。 -/
theorem modPMap_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (modPMap p f) :=
  Ideal.quotientMap_surjective hf

variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- p進完備な環間の環準同型はuntiltと可換する。 -/
theorem untilt_map (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (Perfection.map p (modPMap p f) x) = f x.untilt := by
  change Perfection.teichmullerFun (Perfection.map p (modPMap p f) x) = f x.untilt
  apply Perfection.teichmullerFun_spec
  intro n
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f z, ?_, ?_⟩
  · change Ideal.Quotient.mk (Ideal.span {(p : S)}) (f z) =
      modPMap p f (PreTilt.coeff n x)
    rw [← hz]
    rfl
  · have h := Perfection.teichmullerFun_sModEq hz
    have hm := Ideal.mem_map_of_mem f (SModEq.sub_mem.mp h.symm)
    apply SModEq.sub_mem.mpr
    rw [show x.untilt = Perfection.teichmullerFun x from rfl]
    simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton,
      map_natCast, map_sub, map_pow] using hm

end SerrePositivity

end PerfectoidUntiltNaturalityPart

section PerfectoidTorsionTiltPart

namespace SerrePositivity
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]

/-- mod p写像の核の元には、その核の中でp乗根が存在する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_modPMap_kernel_roots
    (hS : IsIntegralPerfectoid S p) (a : ModP S p)
    (ha : modPMap p (Ideal.Quotient.mk (pTorsionIdeal S p)) a = 0) :
    ∃ b : ModP S p, modPMap p (Ideal.Quotient.mk (pTorsionIdeal S p)) b = 0 ∧ b ^ p = a := by
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  let k := Ideal.Quotient.mk (Ideal.span {(p : S)})
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : q x ∈ Ideal.span {(p : S ⧸ pTorsionIdeal S p)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  let t := x - (p : S) * c
  have ht : (p : S) * t = 0 := by
    apply (mem_pTorsionIdeal S p t).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x - (p : S) * c) = 0
    rw [map_sub, map_mul, map_natCast, hc, sub_self]
  obtain ⟨y, hy, hyp⟩ := hS.exists_p_torsion_p_root S p t ht
  have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hkp : k (p : S) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have htx : k t = k x := by
    dsimp only [t]
    rw [map_sub, map_mul, hkp, zero_mul, sub_zero]
  refine ⟨k y, ?_, ?_⟩
  · change Ideal.Quotient.mk (Ideal.span {(p : S ⧸ pTorsionIdeal S p)}) (q y) = 0
    rw [hqy, map_zero]
  · rw [← map_pow, hyp, htx]

variable [Fact (¬ IsUnit (p : S))]
    [Fact (¬ IsUnit (p : S ⧸ pTorsionIdeal S p))]

/-- pねじれ商のtiltの第0射影の核は、元の第0射影の核の像である。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_preTilt_coeff_kernel
    (hS : IsIntegralPerfectoid S p) :
    (RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p)).map
      (Perfection.map p (modPMap p (Ideal.Quotient.mk (pTorsionIdeal S p)))) =
      RingHom.ker (PreTilt.coeff 0 : PreTilt (S ⧸ pTorsionIdeal S p) p →+*
        ModP (S ⧸ pTorsionIdeal S p) p) :=
  perfection_map_coeff_zero_kernel p (modPMap p (Ideal.Quotient.mk (pTorsionIdeal S p)))
    (modPMap_surjective p _ Ideal.Quotient.mk_surjective) (hS.pTorsionQuotient_modPMap_kernel_roots S p)

end SerrePositivity

end PerfectoidTorsionTiltPart

section PerfectoidTorsionPerfectoidPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- 整perfectoid環のpねじれ商は整perfectoid。四条件から証明する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isIntegralPerfectoid
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    exact Or.inl inferInstance
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨hp, hc, ⟨π, u, hπ⟩, hF, hker⟩ := hdata
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  let := hc
  let Q := S ⧸ pTorsionIdeal S p
  let f := Ideal.Quotient.mk (pTorsionIdeal S p)
  let hcQ : IsAdicComplete (Ideal.span {(p : Q)}) Q := hS.pTorsionQuotient_isAdicComplete S p
  by_cases hsub : Subsingleton Q
  · exact Or.inl hsub
  have hpQ : ¬ IsUnit (p : Q) := by
    intro hu
    have ht : Ideal.span {(p : Q)} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    have hh : IsHausdorff (⊤ : Ideal Q) Q := ht ▸ hcQ.toIsHausdorff
    exact hsub hh.subsingleton
  let : Fact (¬ IsUnit (p : Q)) := ⟨hpQ⟩
  obtain ⟨q, v, a, hq, ha0, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hπ
  have htiltS := tilt_coeff_kernel_eq_span_of_fontaine_generator S p hF q a ha0 hgen
  let g : PreTilt S p →+* PreTilt Q p := Perfection.map p (modPMap p (Ideal.Quotient.mk (pTorsionIdeal S p)))
  let qQ : PreTilt Q p := g q
  have htiltQ : RingHom.ker (PreTilt.coeff 0 : PreTilt Q p →+* ModP Q p) =
      Ideal.span {qQ ^ p} := by
    have hh := hS.pTorsionQuotient_preTilt_coeff_kernel S p
    change (RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p)).map g =
      RingHom.ker (PreTilt.coeff 0 : PreTilt Q p →+* ModP Q p) at hh
    rw [htiltS, Ideal.map_span, Set.image_singleton, map_pow] at hh
    exact hh.symm
  let uQ : Qˣ := Units.map f.toMonoidHom u
  let vQ : Qˣ := Units.map f.toMonoidHom v
  have hπQ : (p : Q) = uQ * (f π) ^ p := by
    change (p : Q) = f (u : S) * (f π) ^ p
    simpa only [map_mul, map_pow, map_natCast] using congrArg f hπ
  have hqQ : qQ.untilt = vQ * f π := by
    change PreTilt.untilt (Perfection.map p (modPMap p f) q) = f (v : S) * f π
    rw [untilt_map, hq, map_mul]
  let w : Qˣ := uQ * (vQ⁻¹) ^ p
  have hpq : (p : Q) = (w : Q) * qQ.untilt ^ p := by
    rw [hqQ, mul_pow, hπQ]
    change (uQ : Q) * (f π) ^ p =
      ((uQ : Q) * (↑(vQ⁻¹) : Q) ^ p) * ((vQ : Q) ^ p * (f π) ^ p)
    calc
      _ = (uQ : Q) * (((↑(vQ⁻¹) : Q) * (vQ : Q)) ^ p * (f π) ^ p) := by simp
      _ = _ := by simp only [mul_pow]; ring
  have hFQ := hS.surjective_pow_mod_p_quotient S p (pTorsionIdeal S p)
  obtain ⟨b, hb⟩ := surjective_fontaineTheta hFQ (-(w : Q))
  have hb0 : IsUnit (b.coeff 0) := by
    apply perfection_isUnit_of_coeff_zero (ModP Q p) p
    change IsUnit (PreTilt.coeff 0 (b.coeff 0))
    rw [← WittVector.mk_fontaineTheta, hb]
    exact (w.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : Q)}))
  have hξ : WittVector.fontaineTheta Q p
      ((p : WittVector p (PreTilt Q p)) + WittVector.teichmuller p qQ ^ p * b) = 0 := by
    rw [map_add, map_mul, map_pow, map_natCast, WittVector.fontaineTheta_teichmuller, hb, hpq]
    ring
  have hkerQ : (RingHom.ker (WittVector.fontaineTheta Q p)).IsPrincipal := by
    rw [ker_fontaineTheta_eq_span_of_tilt_coeff_kernel Q p
      (hS.pTorsionQuotient_p_mul_injective S p) qQ b hb0 hξ htiltQ]
    infer_instance
  exact Or.inr ⟨hpQ, hcQ, ⟨f π, uQ, hπQ⟩, hFQ, hkerQ⟩

end SerrePositivity

end PerfectoidTorsionPerfectoidPart
