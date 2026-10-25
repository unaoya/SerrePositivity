module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring

/-!
# André E1・E2：正則な生成元の全冪商の有界ねじれ

## 概要

d が正則で B/(d) の a 冪ねじれが a^N で消えるなら、B/(d^m) の a 冪ねじれは
a^(N*m) で消える。BS Rem 7.15（著者版 p.62）の有界試験 prism の完備性への入力。

## 方針

a^N x=d y と書き、d の消去で y の一段低い冪商に帰着する。
原典とは異なる主イデアルの可除性による帰納計算。

## 規約

a の正則性・素数性・δ 構造は不要。零冪商と N=0 も含む。

## 使われ方

有界 prism 商の p 冪ねじれを全生成元冪商へ移し、古典的 (p,d) 完備性を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommRing B]

/-- 概要：一乗商でのねじれの有界指数 N は m 乗商で N*m となる。
方針：a^N x=d y と書き、d の正則性による消去と m に関する帰納法を使う。
規約：可除性として述べ、係数元 a には制約しない。
使われ方：BS Rem 7.15（著者版 p.62）の全冪商における有界ねじれ。 -/
theorem regular_power_quotient_torsion_bound_dvd (a d : B)
    (hd : Function.Injective (fun x : B => d * x)) (N : ℕ)
    (hN : ∀ k : ℕ, ∀ x : B, d ∣ a ^ k * x → d ∣ a ^ N * x)
    (m k : ℕ) (x : B) (hx : d ^ m ∣ a ^ k * x) : d ^ m ∣ a ^ (N * m) * x := by
  induction m generalizing k x with
  | zero => simp
  | succ m ih =>
    have hdx : d ∣ a ^ k * x := (dvd_pow_self d (Nat.succ_ne_zero m)).trans hx
    obtain ⟨y, hy⟩ := hN k x hdx
    obtain ⟨z, hz⟩ := hx
    have hdy : d * (a ^ k * y) = d * (d ^ m * (a ^ N * z)) := by
      calc
        _ = a ^ k * (d * y) := by ring
        _ = a ^ k * (a ^ N * x) := by rw [← hy]
        _ = a ^ N * (a ^ k * x) := by ring
        _ = a ^ N * (d ^ (m + 1) * z) := by rw [hz]
        _ = _ := by rw [pow_succ]; ring
    have hydiv : d ^ m ∣ a ^ k * y := ⟨a ^ N * z, hd hdy⟩
    obtain ⟨w, hw⟩ := ih k y hydiv
    refine ⟨w, ?_⟩
    calc
      a ^ (N * (m + 1)) * x = a ^ (N * m) * (a ^ N * x) := by
        rw [Nat.mul_succ, pow_add]
        ring
      _ = a ^ (N * m) * (d * y) := by rw [hy]
      _ = d * (a ^ (N * m) * y) := by ring
      _ = d * (d ^ m * w) := by rw [hw]
      _ = d ^ (m + 1) * w := by rw [pow_succ]; ring

/-- 概要：正則生成元の m 乗商の a 冪ねじれは、一乗商の有界指数の m 倍で消える。
方針：商での零を主イデアルの可除性に戻し、一般の帰納計算を適用する。
規約：素数性・p 正則性を要求せず、元の実商環を使う。
使われ方：BS Rem 7.15（著者版 p.62）の有界試験 prism の全冪商の完備性。 -/
theorem regular_power_quotient_torsion_bound (a d : B)
    (hd : Function.Injective (fun x : B => d * x)) (N : ℕ)
    (hN : ∀ k : ℕ, ∀ x : B ⧸ Ideal.span {d},
      (Ideal.Quotient.mk (Ideal.span {d}) a) ^ k * x = 0 →
        (Ideal.Quotient.mk (Ideal.span {d}) a) ^ N * x = 0)
    (m k : ℕ) (x : B ⧸ Ideal.span {d ^ m})
    (hx : (Ideal.Quotient.mk (Ideal.span {d ^ m}) a) ^ k * x = 0) :
    (Ideal.Quotient.mk (Ideal.span {d ^ m}) a) ^ (N * m) * x = 0 := by
  have hNdvd : ∀ k : ℕ, ∀ y : B, d ∣ a ^ k * y → d ∣ a ^ N * y := by
    intro k y hy
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := hN k (Ideal.Quotient.mk (Ideal.span {d}) y)
      (by simpa only [map_pow, map_mul] using
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hy))
    simpa only [map_pow, map_mul] using hz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : d ^ m ∣ a ^ k * y := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow, map_mul] using hx))
  have hz := regular_power_quotient_torsion_bound_dvd a d hd N hNdvd m k y hy
  simpa only [map_pow, map_mul] using
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hz)

end SerrePositivity.BhattScholze.Andre
