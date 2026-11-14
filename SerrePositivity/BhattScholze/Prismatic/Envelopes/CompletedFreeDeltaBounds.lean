module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import Mathlib.Algebra.MvPolynomial.Cardinal

/-!
# 完備自由 δ 環の正則性と濃度

## 概要
有界な向き付き prism の生成元は完備自由 δ 環で正則であり、候補環の濃度は可算冪で抑えられる。

## 方針
先に p 完備化する。列による表示で関係式を生成元で割る際に、商の有界ねじれを使う。
次いで生成元による完備化は正則性を保つ。濃度は各完備化の列の商表示から評価する。

## 使われ方
変数に沿う prismatic envelope の候補を prism にし、affine 模型の濃度を評価する。
-/

public section

universe u

open CategoryTheory SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

private theorem reflection_smul_injective {R : Type u} [CommRing R] (a d : R)
    (hreg : Function.Injective (d * ·))
    (hB : ∃ N : ℕ, ∀ (n : ℕ) (x : R ⧸ Ideal.span {d}),
      (Ideal.Quotient.mk _ a) ^ n * x = 0 → (Ideal.Quotient.mk _ a) ^ N * x = 0) :
    Function.Injective (fun x : PrincipalReflectionModule R a => d • x) := by
  let L := principalReflectionRelation R a
  let q := Ideal.Quotient.mk (Ideal.span {d})
  obtain ⟨N, hN⟩ := hB
  suffices h : ∀ x : PrincipalReflectionModule R a, d • x = 0 → x = 0 by
    intro x y hxy
    change d • x = d • y at hxy
    exact sub_eq_zero.mp (h _ (by rw [smul_sub, hxy, sub_self]))
  intro x hx
  obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective L.range) x
  change d • principalReflectionMk R a v = 0 at hx
  rw [← map_smul] at hx
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
  change L w = d • v at hw
  have hstep : ∀ n, q (w n) = q a * q (w (n + 1)) := by
    intro n
    have h := congrArg (fun z : ℕ → R => q (z (n + 1))) hw
    simpa [L, principalReflectionRelation, Pi.smul_apply, smul_eq_mul, q] using
      (sub_eq_zero.mp (by simpa [L, principalReflectionRelation, Pi.smul_apply, smul_eq_mul, q]
        using h : q (w n) - q a * q (w (n + 1)) = 0))
  have hzero : q a * q (w 0) = 0 := by
    have h := congrArg (fun z : ℕ → R => q (z 0)) hw
    simpa [L, principalReflectionRelation, Pi.smul_apply, smul_eq_mul, q] using h
  have ht (n : ℕ) : q a ^ (n + 1) * q (w n) = 0 := by
    induction n with
    | zero => simpa using hzero
    | succ n ih => rwa [pow_succ, mul_assoc, ← hstep]
  have hshift (n k : ℕ) : q (w n) = q a ^ k * q (w (n + k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        q (w n) = q a ^ k * q (w (n + k)) := ih
        _ = q a ^ k * (q a * q (w (n + k + 1))) := by rw [← hstep]
        _ = q a ^ (k + 1) * q (w (n + (k + 1))) := by
          rw [pow_succ, mul_assoc]
          rfl
  have hqw (n : ℕ) : q (w n) = 0 :=
    (hshift n N).trans (hN (n + N + 1) _ (ht (n + N)))
  have hdvd (n : ℕ) : ∃ z, w n = d * z := by
    have h := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp (hqw n))
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz⟩
  choose z hz using hdvd
  have hwz : w = d • z := funext hz
  have hv : L z = v := by
    rw [hwz, map_smul] at hw
    funext n
    exact hreg (congrFun hw n)
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, hv⟩

private theorem completion_mul_injective {R : Type u} [CommRing R] (a d : R)
    (hreg : Function.Injective (d * ·))
    (hB : ∃ N : ℕ, ∀ (n : ℕ) (x : R ⧸ Ideal.span {d}),
      (Ideal.Quotient.mk _ a) ^ n * x = 0 → (Ideal.Quotient.mk _ a) ^ N * x = 0) :
    letI := principalCompletionCommRing R a
    Function.Injective (principalCompletionUnitRingHom R a d * ·) := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  intro x y hxy
  change principalCompletionUnitRingHom R a d * x =
    principalCompletionUnitRingHom R a d * y at hxy
  change algebraMap R (PrincipalCompletionH0 R a) d * x =
    algebraMap R (PrincipalCompletionH0 R a) d * y at hxy
  rw [← Algebra.smul_def, ← Algebra.smul_def] at hxy
  let e := principalCompletionH0Equiv R a
  apply e.injective
  apply reflection_smul_injective a d hreg hB
  change d • e x = d • e y
  rw [← e.map_smul, ← e.map_smul, hxy]

private theorem polynomial_quotient_bounded {A σ : Type u} [CommRing A] (p : ℕ) (d : A)
    (h : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ Ideal.span {d}),
      (p : A ⧸ Ideal.span {d}) ^ n * x = 0 → (p : A ⧸ Ideal.span {d}) ^ N * x = 0) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : MvPolynomial σ A ⧸ Ideal.span {MvPolynomial.C d}),
      (Ideal.Quotient.mk _ (p : MvPolynomial σ A)) ^ n * x = 0 →
        (Ideal.Quotient.mk _ (p : MvPolynomial σ A)) ^ N * x = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n x => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  intro hf
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, MvPolynomial.C_dvd_iff_dvd_coeff] at hf ⊢
  intro m
  have hcoeff (k : ℕ) :
      (((p : MvPolynomial σ A) ^ k) * f).coeff m = (p : A) ^ k * f.coeff m := by
    rw [← map_natCast MvPolynomial.C, ← map_pow, MvPolynomial.coeff_C_mul]
  have hm := hf m
  rw [hcoeff] at hm ⊢
  let q := Ideal.Quotient.mk (Ideal.span {d})
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q ((p : A) ^ N * f.coeff m) = 0
  rw [map_mul, map_pow, map_natCast]
  apply hN n
  have hh := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hm)
  simpa only [map_mul, map_pow, map_natCast] using hh

/-- 有界な向き付き prism の生成元の像は、完備自由 δ 環で正則。 -/
theorem completedFreeDelta_generator_regular {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (S : Type u) :
    Function.Injective (completedFreeDeltaBase P S P.generator * ·) := by
  let R := RelativeFreeDeltaRing (R := A) S
  let d : R := MvPolynomial.C P.generator
  have hreg : Function.Injective (d * ·) := by
    intro f g h
    apply MvPolynomial.ext
    intro m
    apply P.generator_regular
    have hm := congrArg (fun f : R => f.coeff m) h
    change (MvPolynomial.C P.generator * (f : MvPolynomial (S × ℕ) A)).coeff m =
      (MvPolynomial.C P.generator * (g : MvPolynomial (S × ℕ) A)).coeff m at hm
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at hm
    exact hm
  let R₁ := PrincipalCompletionH0 R (p : R)
  let : CommRing R₁ := principalCompletionCommRing R (p : R)
  let d₁ : R₁ := principalCompletionUnitRingHom R (p : R) d
  have hreg₁ : Function.Injective (d₁ * ·) :=
    completion_mul_injective (p : R) d hreg (polynomial_quotient_bounded p P.generator hP)
  have hreg₂ := completion_mul_injective d₁ d₁ hreg₁ (by
    refine ⟨1, fun _ x _ => ?_⟩
    rw [pow_one, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul])
  let : CommRing (PDCompletionH0 R p d) := pdCompletionCommRing R p d
  let : CommRing (IteratedCompletionH0 R (p : R) d) := iteratedCompletionCommRing R (p : R) d
  let e := pdCompletionIteratedEquiv R p d
  intro x y hxy
  apply e.injective
  apply hreg₂
  change completedFreeDeltaBase P S P.generator * x =
    completedFreeDeltaBase P S P.generator * y at hxy
  let c : PDCompletionH0 R p d := pdCompletionUnit R p d d
  let x' : PDCompletionH0 R p d := x
  let y' : PDCompletionH0 R p d := y
  have he : e (c * x') = e (c * y') := congrArg e (show c * x' = c * y' from hxy)
  rw [map_mul, map_mul] at he
  have hunit : e c = principalCompletionUnitRingHom R₁ d₁ d₁ :=
    pdCompletionIteratedEquiv_unit R p d d
  rwa [hunit] at he

open Cardinal in
private theorem cardinal_principalCompletionH0_le {R : Type u} [CommRing R] (a : R) :
    #(PrincipalCompletionH0 R a) ≤ #R ^ ℵ₀ := by
  let e := (principalCompletionH0Equiv R a).symm
  have h := Cardinal.mk_le_of_surjective (e.surjective.comp
    (Submodule.Quotient.mk_surjective (principalReflectionRelation R a).range))
  simpa [Cardinal.mk_arrow, Cardinal.mk_nat] using h

open Cardinal in
/-- 完備自由 δ 環は多項式の二段の列の商なので、濃度は可算冪で抑えられる。 -/
theorem cardinal_envelope_le {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (P : OrientedPrism p A) (S : Type u) :
    Cardinal.mk (completedFreeDelta P S) ≤ (Cardinal.mk A + Cardinal.mk S + ℵ₀) ^ ℵ₀ := by
  let R := RelativeFreeDeltaRing (R := A) S
  let d : R := algebraMap A R P.generator
  let B := PrincipalCompletionH0 R (p : R)
  let : CommRing B := principalCompletionCommRing R (p : R)
  let dB : B := principalCompletionUnitRingHom R (p : R) d
  let κ := #A + #S + ℵ₀
  have hA : #A ≤ κ := (self_le_add_right _ _).trans (self_le_add_right _ _)
  have hS : #S ≤ κ := (self_le_add_left _ _).trans (self_le_add_right _ _)
  have hN : ℵ₀ ≤ κ := self_le_add_left _ _
  have hR : #R ≤ κ := by
    apply MvPolynomial.cardinalMk_le_max.trans
    refine sup_le (sup_le hA ?_) hN
    simp only [mk_prod, lift_uzero, mk_nat, lift_aleph0]
    exact (mul_le_max_of_aleph0_le_right le_rfl).trans (max_le hS hN)
  have hB : #B ≤ κ ^ ℵ₀ :=
    (cardinal_principalCompletionH0_le (p : R)).trans (power_le_power_right hR)
  let : CommRing (PDCompletionH0 R p d) := pdCompletionCommRing R p d
  let : CommRing (IteratedCompletionH0 R (p : R) d) := iteratedCompletionCommRing R (p : R) d
  let e := pdCompletionIteratedEquiv R p d
  calc
    #(completedFreeDelta P S) = #(PrincipalCompletionH0 B dB) := mk_congr e.toEquiv
    _ ≤ #B ^ ℵ₀ := cardinal_principalCompletionH0_le dB
    _ ≤ (κ ^ ℵ₀) ^ ℵ₀ := power_le_power_right hB
    _ = κ ^ ℵ₀ := by rw [← power_mul, mul_aleph0_eq le_rfl]

end SerrePositivity.BhattScholze.Prismatic
