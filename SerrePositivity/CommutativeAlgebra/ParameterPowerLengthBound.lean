module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelDimension
public import SerrePositivity.CommutativeAlgebra.ParameterPowerMultiplicity

/-! # パラメータの冪による商の長さの多項式評価

## 概要

Noether 局所環 `E` の元 `z_1, …, z_r` が極大イデアル準素なイデアルを生成し、
`dim E ≤ e` なら、定数 `C` があって全ての `v ≥ 1` で `ℓ(E / (z_1^v, …, z_r^v)) ≤ C v^e`。

## 方針

単項式の指数の数え上げから `(z)^{(r+1)v} ⊆ (z^v)` なので、左辺は Samuel 関数
`ℓ(E / (z)^{(r+1)v})` 以下。Samuel 関数は十分先で次数 `dim E` の多項式に一致し
（Hilbert–Samuel の次元定理）、単調なので全ての `n` で `A (N+1)^e (n+1)^e` 以下に抑えられる。

## 使われ方

`formalization-plans/frobenius-koszul-elementary.md` の E4。零でない元 `c` で割った
次元 `h - 1` の環に適用し、`ℓ(R'/(c, Z^q)) = O(q^{h-1})` を得る。
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity

/-- 次数 `d` 以下の有理係数多項式は、非負の点で `A (x + 1)^d` 以下。係数の絶対値の和を `A` にとる。 -/
lemma Polynomial.exists_eval_le_mul_pow (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    ∃ A : ℕ, ∀ x : ℚ, 0 ≤ x → P.eval x ≤ A * (x + 1) ^ d := by
  refine ⟨⌈∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|⌉₊, fun x hx ↦ ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i
        ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * (x + 1) ^ d := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ d := by
        have := Finset.mem_range.mp hi
        omega
      have hpow : x ^ i ≤ (x + 1) ^ d :=
        (pow_le_pow_left₀ hx (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi')
      calc
        P.coeff i * x ^ i ≤ |P.coeff i| * x ^ i :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |P.coeff i| * (x + 1) ^ d := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) * (x + 1) ^ d :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)

variable (E : Type u) [CommRing E] [IsNoetherianRing E] [IsLocalRing E]

/-- Samuel 関数は全ての `n` で `C (n + 1)^e` 以下（`dim E ≤ e`）。十分先では次数 `dim E` の多項式で、
それ以前は単調性で十分先の値に押し上げる。 -/
theorem HilbertSamuel.exists_samuelFunction_le_pow (I : Ideal E)
    (hI : I.radical = maximalIdeal E) (e : ℕ) (hdim : dimToNat (ringKrullDim E) ≤ e) :
    ∃ C : ℕ, ∀ n : ℕ, HilbertSamuel.samuelFunction E I E n ≤ ((C * (n + 1) ^ e : ℕ) : ℕ∞) := by
  have hP := HilbertSamuel.isSamuelPoly_poly_of_radical E I hI E
  have hdeg : (HilbertSamuel.poly E I E).natDegree ≤ e := by
    rw [HilbertSamuel.natDegree_poly_eq_dim E I hI]
    exact hdim
  obtain ⟨A, hA⟩ := Polynomial.exists_eval_le_mul_pow _ e hdeg
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  refine ⟨A * (N + 1) ^ e, fun n ↦ ?_⟩
  set m := max n N
  have hmono := HilbertSamuel.samuelFunction_mono E I (M := E) (le_max_left n N)
  have hm := hN m (le_max_right n N)
  -- 十分先の値は多項式の値
  have hval : (HilbertSamuel.samuelFunction E I E m).toNat ≤ A * (m + 1) ^ e := by
    have h := hA (m : ℚ) (by positivity)
    rw [← hm.2] at h
    exact_mod_cast h
  have hm1 : m + 1 ≤ (N + 1) * (n + 1) := by
    rcases le_total n N with h | h
    · simp only [m, max_eq_right h]
      nlinarith
    · simp only [m, max_eq_left h]
      nlinarith
  have hbound : A * (m + 1) ^ e ≤ A * (N + 1) ^ e * (n + 1) ^ e := by
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm1 e)
  calc
    HilbertSamuel.samuelFunction E I E n ≤ HilbertSamuel.samuelFunction E I E m := hmono
    _ = ((HilbertSamuel.samuelFunction E I E m).toNat : ℕ∞) := (ENat.natCast_toNat hm.1).symm
    _ ≤ _ := by exact_mod_cast hval.trans hbound

/-- **パラメータの冪の商の長さ**：`z` が極大イデアル準素なイデアルを生成し `dim E ≤ e` なら、
定数 `C` があって `v ≥ 1` で `ℓ(E / (z^v)) ≤ C v^e`。`(z)^{(r+1)v} ⊆ (z^v)` と Samuel 関数の評価による。 -/
theorem exists_length_quotient_generator_pow_le {r : ℕ} (z : Fin r → E)
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal E) (e : ℕ)
    (hdim : dimToNat (ringKrullDim E) ≤ e) :
    ∃ C : ℕ, ∀ v : ℕ, 0 < v →
      Module.length E (E ⧸ Ideal.span (Set.range fun i ↦ z i ^ v)) ≤ ((C * v ^ e : ℕ) : ℕ∞) := by
  set I := Ideal.span (Set.range z)
  obtain ⟨C, hC⟩ := HilbertSamuel.exists_samuelFunction_le_pow E I hz e hdim
  refine ⟨C * (r + 2) ^ e, fun v hv ↦ ?_⟩
  -- 冪のイデアルの包含
  have hcont : I ^ ((r + 1) * v) ≤ Ideal.span (Set.range fun i ↦ z i ^ v) := by
    have h := ParameterPowerMultiplicity.span_pow_le_generator_power z v 1 hv
    rw [pow_one, mul_one] at h
    exact (Ideal.pow_le_pow_right (by
      have : r * (v - 1) ≤ r * v := Nat.mul_le_mul_left r (Nat.sub_le v 1)
      nlinarith)).trans h
  have hsub : (I ^ ((r + 1) * v) • ⊤ : Submodule E E) ≤ Ideal.span (Set.range fun i ↦ z i ^ v) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hcont
  have hlen : Module.length E (E ⧸ Ideal.span (Set.range fun i ↦ z i ^ v)) ≤
      HilbertSamuel.samuelFunction E I E ((r + 1) * v) :=
    Module.length_le_of_surjective (Submodule.factor hsub) (Submodule.factor_surjective hsub)
  refine hlen.trans ((hC _).trans ?_)
  have h1 : (r + 1) * v + 1 ≤ (r + 2) * v := by nlinarith
  have h2 : C * ((r + 1) * v + 1) ^ e ≤ C * (r + 2) ^ e * v ^ e := by
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 e)
  exact_mod_cast h2

end SerrePositivity
