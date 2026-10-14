module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Group.Idempotent

/-! # 剰余環で冪等なイデアル像による零化

剰余環での冪等性を明示仮定として、イデアルの正の冪による零化を
イデアル自体による零化へ戻す。a冪ねじれ加群には元ごとに適用する。
-/

@[expose] public section
universe u v
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- R/Jでの像が冪等なら、正の冪IᵉとJはIを含む。 -/
theorem ideal_le_pow_sup_of_quotient_image_idempotent (I J : Ideal R) (e : ℕ) (he : 0 < e)
    (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk J))) : I ≤ I ^ e ⊔ J := by
  have hp : (I ^ e).map (Ideal.Quotient.mk J) = I.map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_pow, hI.pow_eq (by omega)]
  have h : I.map (Ideal.Quotient.mk J) ≤ (I ^ e).map (Ideal.Quotient.mk J) := hp.ge
  have hc := Ideal.map_le_iff_le_comap.mp h
  simpa only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hc

/-- IᵉとJが一つの元を消すとき、R/Jでの像の冪等性によりIもその元を消す。 -/
theorem smul_eq_zero_of_ideal_pow_and_quotient_image_idempotent
    {M : Type v} [AddCommGroup M] [Module R M] (I J : Ideal R)
    (e : ℕ) (he : 0 < e) (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk J)))
    (x : M) (hpow : ∀ r ∈ I ^ e, r • x = 0) (hJ : ∀ r ∈ J, r • x = 0)
    (r : R) (hr : r ∈ I) : r • x = 0 := by
  let L : Ideal R := (LinearMap.toSpanSingleton R M x).ker
  have hp : I ^ e ≤ L := fun r hr ↦ hpow r hr
  have hJL : J ≤ L := fun r hr ↦ hJ r hr
  exact (ideal_le_pow_sup_of_quotient_image_idempotent I J e he hI).trans
    (sup_le hp hJL) hr

/-- 全加群がJで消える場合の、正の冪による零化からIによる零化への一般形。 -/
theorem ideal_annihilates_of_pow_annihilates_mod
    {M : Type v} [AddCommGroup M] [Module R M] (I J : Ideal R)
    (e : ℕ) (he : 0 < e) (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk J)))
    (hpow : ∀ r ∈ I ^ e, ∀ x : M, r • x = 0)
    (hJ : ∀ r ∈ J, ∀ x : M, r • x = 0) : ∀ r ∈ I, ∀ x : M, r • x = 0 := by
  intro r hr x
  exact smul_eq_zero_of_ideal_pow_and_quotient_image_idempotent I J e he hI x
    (fun s hs ↦ hpow s hs x) (fun s hs ↦ hJ s hs x) r hr

/-- aⁿで消える加群に対する有限段の形。aの正則性は不要。 -/
theorem ideal_annihilates_of_pow_annihilates_and_principal_torsion
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) (a : R) (n : ℕ)
    (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (e : ℕ) (he : 0 < e) (hpow : ∀ r ∈ I ^ e, ∀ x : M, r • x = 0)
    (htorsion : ∀ x : M, a ^ n • x = 0) : ∀ r ∈ I, ∀ x : M, r • x = 0 := by
  intro r hr x
  let L : Ideal R := (LinearMap.toSpanSingleton R M x).ker
  have hJL : Ideal.span {a ^ n} ≤ L :=
    (Ideal.span_singleton_le_iff_mem L).mpr (htorsion x)
  exact smul_eq_zero_of_ideal_pow_and_quotient_image_idempotent I _ e he hI x
    (fun s hs ↦ hpow s hs x) (fun s hs ↦ hJL hs) r hr

/-- 各mod aⁿで像が冪等なIについて、a冪ねじれ加群上のIᵉ零化をI零化へ戻す。
元ごとのねじれ指数だけを使い、加群全体の一様なa指数は要求しない。 -/
theorem ideal_annihilates_of_pow_annihilates_and_powerTorsion
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) (a : R)
    (hI : ∀ n : ℕ, 0 < n → IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (e : ℕ) (he : 0 < e) (hpow : ∀ r ∈ I ^ e, ∀ x : M, r • x = 0)
    (htorsion : ∀ x : M, ∃ n : ℕ, a ^ n • x = 0) : ∀ r ∈ I, ∀ x : M, r • x = 0 := by
  intro r hr x
  obtain ⟨n, hn⟩ := htorsion x
  have hn' : a ^ (n + 1) • x = 0 := by rw [pow_succ', mul_smul, hn, smul_zero]
  let L : Ideal R := (LinearMap.toSpanSingleton R M x).ker
  have hJL : Ideal.span {a ^ (n + 1)} ≤ L :=
    (Ideal.span_singleton_le_iff_mem L).mpr hn'
  exact smul_eq_zero_of_ideal_pow_and_quotient_image_idempotent I _ e he
    (hI (n + 1) (by omega)) x (fun s hs ↦ hpow s hs x) (fun s hs ↦ hJL hs) r hr

end SerrePositivity
