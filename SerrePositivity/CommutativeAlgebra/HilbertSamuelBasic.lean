module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Hilbert–Samuel 理論の基本定義

Samuel 関数、多項式で表される条件、その多項式の一意性と選択、重複度を定義する。
商の有限長性、Samuel 関数の単調性と正値性、最高次係数の正値性も証明する。
多項式の存在・次元定理には依存しない。

随伴次数加群と Hilbert 級数の構成はこのファイルを基礎とする。
一般の多項式性・次元定理とその帰結は `HilbertSamuel.lean` に置く。
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity

namespace HilbertSamuel

variable (D : Type u) [CommRing D]

/-- Samuel 関数 `n ↦ ℓ_D(M / I^n M)`。 -/
noncomputable def samuelFunction (I : Ideal D) (M : Type u) [AddCommGroup M] [Module D M]
    (n : ℕ) : ℕ∞ :=
  Module.length D (M ⧸ (I ^ n • ⊤ : Submodule D M))

/-- 多項式 `P ∈ ℚ[X]` が Samuel 関数を表すこと：十分大きい `n` で `ℓ(M/I^n M)` は有限で
`P(n)` に等しい。 -/
def IsSamuelPoly (I : Ideal D) (M : Type u) [AddCommGroup M] [Module D M] (P : ℚ[X]) : Prop :=
  ∀ᶠ n in Filter.atTop,
    samuelFunction D I M n ≠ ⊤ ∧ ((samuelFunction D I M n).toNat : ℚ) = P.eval (n : ℚ)

variable {D}

/-- Samuel 関数を表す多項式は一意（無限個の自然数で値が一致する）。 -/
lemma IsSamuelPoly.unique {I : Ideal D} {M : Type u} [AddCommGroup M] [Module D M]
    {P Q : ℚ[X]} (hP : IsSamuelPoly D I M P) (hQ : IsSamuelPoly D I M Q) : P = Q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hP.and hQ)
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ioi_infinite N).image Nat.cast_injective.injOn).mono
  rintro _ ⟨n, hn, rfl⟩
  have := hN n (le_of_lt hn)
  change P.eval (n : ℚ) = Q.eval (n : ℚ)
  rw [← this.1.2, this.2.2]

variable (D)

open Classical in
/-- Samuel 関数を表す多項式（存在すればそれ、なければ `0`）。 -/
noncomputable def poly (I : Ideal D) (M : Type u) [AddCommGroup M] [Module D M] : ℚ[X] :=
  if h : ∃ P : ℚ[X], IsSamuelPoly D I M P then h.choose else 0

/-- 表す多項式が存在すれば、`poly` がそれ。 -/
lemma isSamuelPoly_poly {I : Ideal D} {M : Type u} [AddCommGroup M] [Module D M]
    (h : ∃ P : ℚ[X], IsSamuelPoly D I M P) : IsSamuelPoly D I M (poly D I M) := by
  simp only [poly, h, dite_true]
  exact Exists.choose_spec _

/-- 表す多項式 `P` があれば `poly = P`。 -/
lemma poly_eq {I : Ideal D} {M : Type u} [AddCommGroup M] [Module D M] {P : ℚ[X]}
    (hP : IsSamuelPoly D I M P) : poly D I M = P :=
  (isSamuelPoly_poly D ⟨P, hP⟩).unique hP

section powers

variable (M : Type u) [AddCommGroup M] [Module D M]

/-- Samuel 関数は指数について単調増加する。商の間の全射で長さを比較する。 -/
lemma samuelFunction_mono (I : Ideal D) : Monotone (samuelFunction D I M) := by
  intro m n hmn
  have h : (I ^ n • ⊤ : Submodule D M) ≤ I ^ m • ⊤ :=
    Submodule.smul_mono (Ideal.pow_le_pow_right hmn) le_rfl
  exact Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

/-- イデアルを大きくすると Samuel 関数は小さくなる。 -/
lemma samuelFunction_antitone_ideal (n : ℕ) :
    Antitone (fun I : Ideal D => samuelFunction D I M n) := by
  intro I J hIJ
  have h : (I ^ n • ⊤ : Submodule D M) ≤ J ^ n • ⊤ :=
    Submodule.smul_mono (Ideal.pow_right_mono hIJ n) le_rfl
  exact Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

/-- イデアル自体を冪にすることは、Samuel 関数の添字の倍率変更に当たる。 -/
lemma samuelFunction_pow (I : Ideal D) (v n : ℕ) :
    samuelFunction D (I ^ v) M n = samuelFunction D I M (v * n) := by
  unfold samuelFunction
  rw [← pow_mul]

/-- `I` の Samuel 多項式が `P(X)` なら、`I^v` のものは `P(vX)`。 -/
lemma IsSamuelPoly.pow {I : Ideal D} {P : ℚ[X]} (hP : IsSamuelPoly D I M P)
    (v : ℕ) (hv : 0 < v) : IsSamuelPoly D (I ^ v) M (P.comp (C (v : ℚ) * X)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have h := hN (v * n) (hn.trans (Nat.le_mul_of_pos_left n hv))
  rw [samuelFunction_pow D M]
  refine ⟨h.1, ?_⟩
  simpa only [eval_comp, eval_mul, eval_C, eval_X, Nat.cast_mul] using h.2

end powers

/-- **Hilbert–Samuel 重複度** `e(I, M) := d! · (poly I M).coeff d`、`d = dim M`。
`M = D`、`I` が `m_D` 準素なら、`poly` の次数は `dim D` なので最高次係数の `d!` 倍。 -/
noncomputable def multiplicity (I : Ideal D) (M : Type u) [AddCommGroup M] [Module D M] : ℚ :=
  let d := dimToNat (Module.supportDim D M)
  (d.factorial : ℚ) * (poly D I M).coeff d

/-! ## Samuel 関数の性質と、多項式性・次元定理の未証明箇所 -/

section statements

variable [IsNoetherianRing D] [IsLocalRing D]

/-- **有限性**：`I` が `m_D` 準素（`√I = m_D`）で `M` が有限生成なら `ℓ(M/I^n M) < ∞`。
`M/I^n M` は `I^n` で消える有限生成加群で、`D/I` は Artin 環なので有限長
（`isFiniteLength_of_le_radical_annihilator`）。 -/
theorem samuelFunction_ne_top (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M] (n : ℕ) :
    samuelFunction D I M n ≠ ⊤ := by
  have hArt : IsArtinianRing (D ⧸ I) := by
    have : IsArtinianRing (D ⧸ maximalIdeal D) := inferInstanceAs (IsArtinianRing (ResidueField D))
    exact isArtinianRing_quotient_of_le_radical (maximalIdeal D) I (by rw [hI])
  have hann : I ^ n ≤ Module.annihilator D (M ⧸ (I ^ n • ⊤ : Submodule D M)) := by
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hle : I ≤ (Module.annihilator D (M ⧸ (I ^ n • ⊤ : Submodule D M))).radical := by
    intro a ha
    exact Ideal.mem_radical_iff.mpr ⟨n, hann (Ideal.pow_mem_pow ha n)⟩
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_of_le_radical_annihilator I (M ⧸ (I ^ n • ⊤ : Submodule D M)) hle)

omit [IsNoetherianRing D] in
/-- 正の指数では、準素イデアルによる環の商は非零なので Samuel 関数は正。 -/
lemma samuelFunction_pos (I : Ideal D) (hI : I.radical = maximalIdeal D)
    {n : ℕ} (hn : 0 < n) : 0 < samuelFunction D I D n := by
  have hproper : I ^ n ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal D).ne_top
    ((Ideal.pow_le_self hn.ne').trans (Ideal.le_radical.trans_eq hI))
  let : Nontrivial (D ⧸ I ^ n) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hs : (I ^ n • ⊤ : Submodule D D) = I ^ n :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  unfold samuelFunction
  rw [hs]
  exact Module.length_pos

omit [IsNoetherianRing D] in
/-- Samuel 多項式の最高次係数は正。次数の値は使わず、十分先での値の正値性から導く。 -/
lemma IsSamuelPoly.leadingCoeff_pos {I : Ideal D} {P : ℚ[X]} (hI : I.radical = maximalIdeal D)
    (hP : IsSamuelPoly D I D P) : 0 < P.leadingCoeff := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ) := by
    filter_upwards [hP, eventually_gt_atTop 0] with n hn hnpos
    rw [← hn.2]
    exact Nat.cast_pos.mpr (ENat.toNat_pos (samuelFunction_pos D I hI hnpos).ne' hn.1)
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨n, hn⟩ := hpos.exists
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C] at hn
    simpa only [leadingCoeff, hdeg] using hn
  · by_contra! hlc
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)) hlc).comp
        (tendsto_natCast_atTop_atTop (R := ℚ))
    obtain ⟨n, hn, hn'⟩ := (hpos.and (ht.eventually_lt_atBot 0)).exists
    exact (lt_trans hn hn').false

end statements

end HilbertSamuel

end SerrePositivity
