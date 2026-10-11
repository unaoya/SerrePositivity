module

public import SerrePositivity.CommutativeAlgebra.ReesModule
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-! # Hilbert 級数から Samuel 多項式への接続

随伴次数加群の長さの級数を定義し、Samuel 関数の級数が
`X/(1-X)` 倍となることを証明する。
Hilbert 級数の有理型表示 `Q(X)/(1-X)^s` が得られれば、次数 s 以下の
Samuel 多項式を Mathlib の `Polynomial.hilbertPoly` から構成する。
有理型表示の存在は `HilbertSamuelPolynomial.lean` で証明する。
このファイルは有理型表示から多項式への接続を扱う。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

open IsLocalRing Polynomial Filter

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- `Σ length(I^nM/I^(n+1)M) X^n`。有限長のとき実際の長さを係数とする。 -/
def hilbertSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((hilbertFunction R I M n).toNat : ℚ)

/-- `Σ length(M/I^nM) X^n`。定数項は零。 -/
def samuelSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((samuelFunction R I M n).toNat : ℚ)

/-- Hilbert 多項式の標準構成は、分母の指数 s+1 に対して次数 s 以下。 -/
lemma natDegree_hilbertPoly_succ_le (Q : ℚ[X]) (s : ℕ) :
    (Polynomial.hilbertPoly Q (s + 1)).natDegree ≤ s := by
  by_cases h : Polynomial.hilbertPoly Q (s + 1) = 0
  · simp [h]
  · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero h]
    omega

section finiteLength

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
variable (hI : I.radical = maximalIdeal R)

include hI

/-- 増分の公式を母関数の等式に書き換える。 -/
theorem one_sub_X_mul_samuelSeries :
    (1 - PowerSeries.X) * samuelSeries R I M = PowerSeries.X * hilbertSeries R I M := by
  ext n
  cases n with
  | zero => simp [samuelSeries, samuelFunction_zero]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      samuelSeries, hilbertSeries, PowerSeries.coeff_mk]
    rw [samuelFunction_succ, ENat.toNat_add
      (hilbertFunction_ne_top R I M hI n) (samuelFunction_ne_top R I hI M n)]
    push_cast
    ring

/-- Samuel 関数の級数は Hilbert 級数に `X/(1-X)` を掛けたもの。 -/
theorem samuelSeries_eq :
    samuelSeries R I M =
      PowerSeries.X * hilbertSeries R I M * (PowerSeries.invOneSubPow ℚ 1).val := by
  have hinv : (1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
    simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
      (PowerSeries.invOneSubPow ℚ 1).inv_val
  calc
    samuelSeries R I M =
        ((1 - PowerSeries.X) * samuelSeries R I M) *
          (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
    _ = _ := by rw [one_sub_X_mul_samuelSeries R I M hI]

/-- Hilbert 級数の有理型表示から、次数 s 以下の Samuel 多項式を明示的に構成する。
多項式性の既存の `sorry` は使わない。 -/
theorem exists_isSamuelPoly_of_hilbertSeries (s : ℕ) (Q : ℚ[X])
    (hseries : hilbertSeries R I M = Q * (PowerSeries.invOneSubPow ℚ s).val) :
    ∃ P : ℚ[X], IsSamuelPoly R I M P ∧ P.natDegree ≤ s := by
  let P := Polynomial.hilbertPoly (X * Q) (s + 1)
  have hs : samuelSeries R I M =
      (X * Q : ℚ[X]) * (PowerSeries.invOneSubPow ℚ (s + 1)).val := by
    rw [samuelSeries_eq R I M hI, hseries, PowerSeries.invOneSubPow_add, Units.val_mul,
      Polynomial.coe_mul, Polynomial.coe_X]
    ring
  refine ⟨P, ?_, natDegree_hilbertPoly_succ_le (X * Q) s⟩
  filter_upwards [eventually_gt_atTop (X * Q).natDegree] with n hn
  refine ⟨samuelFunction_ne_top R I hI M n, ?_⟩
  have hc := congrArg (PowerSeries.coeff n) hs
  rw [samuelSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (s + 1) hn] at hc
  exact hc

/-- I が冪零なら Samuel 関数は最終的に加群全体の長さとなり、定数多項式で表される。
Hilbert–Serre の零変数の場合に使う境界。 -/
theorem exists_isSamuelPoly_of_pow_eq_zero (k : ℕ) (hk : I ^ k = 0) :
    ∃ P : ℚ[X], IsSamuelPoly R I M P ∧ P.natDegree = 0 := by
  have hvalue (n : ℕ) (hn : k ≤ n) : samuelFunction R I M n = Module.length R M := by
    have hpow : I ^ n = 0 := by
      apply le_antisymm _ bot_le
      exact (Ideal.pow_le_pow_right hn).trans_eq hk
    have hs : (I ^ n • ⊤ : Submodule R M) = ⊥ := by
      rw [hpow, zero_smul]
      rfl
    unfold samuelFunction
    rw [hs]
    exact (Submodule.quotEquivOfEqBot _ rfl).length_eq
  refine ⟨C ((Module.length R M).toNat : ℚ), ?_, by simp⟩
  filter_upwards [eventually_ge_atTop k] with n hn
  refine ⟨samuelFunction_ne_top R I hI M n, ?_⟩
  rw [hvalue n hn, eval_C]

end finiteLength

end SerrePositivity.HilbertSamuel
