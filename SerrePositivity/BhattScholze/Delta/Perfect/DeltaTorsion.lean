module

public import SerrePositivity.BhattScholze.Delta.Distinguished.DeltaPrime
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Frobenius持上げによるpねじれの消去

BS著者版Lemma 2.28の代数的証明。δ(p)≡1 mod pを用いるので、
Z_(p)代数やpのJacobson根基への所属を仮定せず、任意のδ構造で証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- px=0ならφ(x)=0かつp^pδ(x)=0。
δ積公式とφの環準同型則を使い、最後はδ(p)≡1 mod pで消去する（BS Lemma 2.28）。 -/
theorem torsion_calculation (D : DeltaStructure p A) {x : A} (hx : (p : A) * x = 0) :
    D.frobeniusLift x = 0 ∧ (p : A) ^ p * D.delta x = 0 := by
  have hpow (a : A) : a ^ (p - 1) * a = a ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
  have hpx : (p : A) ^ (p - 1) * x = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (show p - 1 ≠ 0 by have := (Fact.out : p.Prime).two_le; omega)
    rw [hn, pow_succ, mul_assoc, hx, mul_zero]
  have hφp : (p : A) * D.frobeniusLift x = 0 := by
    have h := congrArg D.frobeniusLift hx
    simpa only [map_mul, map_natCast, map_zero] using h
  have hφpow : (p : A) ^ (p - 1) * D.frobeniusLift x = 0 := by
    have h := congrArg D.frobeniusLift hpx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using h
  have hxp : (p : A) ^ (p - 1) * x ^ p = 0 := by
    rw [← hpow x]
    calc
      (p : A) ^ (p - 1) * (x ^ (p - 1) * x) =
          x ^ (p - 1) * ((p : A) ^ (p - 1) * x) := by ring
      _ = 0 := by rw [hpx, mul_zero]
  have hpd : (p : A) ^ p * D.delta x = 0 := by
    have h := congrArg (fun a ↦ (p : A) ^ (p - 1) * a) (D.frobeniusLift_apply x)
    rw [hφpow, mul_add, hxp, zero_add, ← mul_assoc, hpow (p : A)] at h
    exact h.symm
  have hδφ : D.delta (p : A) * D.frobeniusLift x = 0 := by
    have h := congrArg D.delta hx
    rw [D.delta_mul, D.delta_zero, hpd, zero_add] at h
    rw [D.frobeniusLift_apply]
    linear_combination h
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp D.delta_p_sub_one_mem
  have hφ : D.frobeniusLift x = 0 := by
    linear_combination hδφ - D.frobeniusLift x * hr - r * hφp
  exact ⟨hφ, hpd⟩

/-- φが単射ならpの乗法は単射（BS Lemma 2.28(1)）。完備性は不要。 -/
theorem p_mul_injective_of_frobeniusLift_injective (D : DeltaStructure p A)
    (hφ : Function.Injective D.frobeniusLift) : Function.Injective (fun x : A ↦ (p : A) * x) := by
  intro x y hxy
  change (p : A) * x = (p : A) * y at hxy
  have hz : (p : A) * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
  have h := (D.torsion_calculation hz).1
  have he : x - y = 0 := hφ (h.trans D.frobeniusLift.map_zero.symm)
  exact sub_eq_zero.mp he

/-- 完全δ環ではpは正則。完全prismとWitt環の比較に使う。 -/
theorem IsPerfect.p_mul_injective {D : DeltaStructure p A} (hD : D.IsPerfect) :
    Function.Injective (fun x : A ↦ (p : A) * x) :=
  D.p_mul_injective_of_frobeniusLift_injective hD.1

/-- 被約δ環ではpの乗法は単射（BS Lemma 2.28(2)）。
p^pδ(x)=0からpδ(x)の冪が零となり、被約性を二度使ってpx=0からx=0を導く。 -/
theorem p_mul_injective_of_isReduced (D : DeltaStructure p A) [IsReduced A] :
    Function.Injective (fun x : A ↦ (p : A) * x) := by
  have hker (x : A) (hx : (p : A) * x = 0) : x = 0 := by
    obtain ⟨hφ, hpd⟩ := D.torsion_calculation hx
    have hpow : D.delta x ^ (p - 1) * D.delta x = D.delta x ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    have hnil : ((p : A) * D.delta x) ^ p = 0 := by
      rw [mul_pow, ← hpow]
      calc
        (p : A) ^ p * (D.delta x ^ (p - 1) * D.delta x) =
            D.delta x ^ (p - 1) * ((p : A) ^ p * D.delta x) := by ring
        _ = 0 := by rw [hpd, mul_zero]
    have hpδ : (p : A) * D.delta x = 0 := eq_zero_of_pow_eq_zero hnil
    have hxp : x ^ p = 0 := by
      simpa only [D.frobeniusLift_apply, hpδ, add_zero] using hφ
    exact eq_zero_of_pow_eq_zero hxp
  intro x y hxy
  change (p : A) * x = (p : A) * y at hxy
  apply sub_eq_zero.mp
  apply hker
  rw [mul_sub, hxy, sub_self]

/-- δ環でpが冪零なら零環である（BS Example 2.6の最後の主張）。
φは自然数pを固定しpねじれを零に送るため、p^n=0から順に指数を下げる。 -/
theorem subsingleton_of_isNilpotent_p (D : DeltaStructure p A)
    (hp : IsNilpotent (p : A)) : Subsingleton A := by
  have hpow (n : ℕ) (hn : (p : A) ^ n = 0) : (1 : A) = 0 := by
    induction n with
    | zero => simpa only [pow_zero] using hn
    | succ n ih =>
        have hx : (p : A) * (p : A) ^ n = 0 := by
          rw [mul_comm, ← pow_succ]
          exact hn
        have h := (D.torsion_calculation hx).1
        have hprev : (p : A) ^ n = 0 := by simpa only [map_pow, map_natCast] using h
        exact ih hprev
  obtain ⟨n, hn⟩ := hp
  exact subsingleton_of_zero_eq_one (hpow n hn).symm

end SerrePositivity.BhattScholze.DeltaStructure
