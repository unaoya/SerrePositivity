module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Hilbert–Samuel 重複度：定義と主張

## 概要

Noether 局所環 `D`、`m_D` 準素イデアル `I`、有限生成 `D` 加群 `M` の Hilbert–Samuel 重複度
`e(I, M)` を標準的に定義する：

- Samuel 関数 `χ(n) = ℓ_D(M / I^n M)`（`ℕ∞` 値）。
- **Hilbert–Samuel の定理**：`χ(n)` は十分大きい `n` で `ℚ` 係数多項式 `P` の値に等しく、
  `P` の次数は `I` の生成元の個数以下。`P` は一意（`HilbertSamuel.poly`）。
- `e(I, M) := d! · (P の X^d の係数)`、`d = dim M`（`Module.supportDim` を自然数に落としたもの）。
  `M = D` なら `d = dim D` で、`P` の次数は `dim D`（次元定理）なので `e(I, D)` は最高次係数の
  `d!` 倍、正の整数。論文の `e((z), D)` はこれ。

## 方針

定義は標準のものを採り、Samuel 関数の多項式性（Hilbert の定理）と
次元定理（`deg P = dim D`）は既存の未証明箇所として残す。正値性は Samuel 関数の正値性から
最高次係数の符号を決定して証明する。多項式の一意性と、存在から定義の
`poly` が実際に Samuel 関数を表すことも証明済み。

以前 `CommutativeAlgebra/Multiplicity.lean` にあった極限の式による定義（極限の存在を仮定しない
junk value つきのもの）は、2026-10-10 にこの定義に置き換えて削除した。

## 内容

- `samuelFunction`、`IsSamuelPoly`、`IsSamuelPoly.unique`、`poly`、`isSamuelPoly_poly`。
- `multiplicity` の定義。
- 証明済み：Samuel 関数の有限性・正値性、多項式の最高次係数の正値性、
  `multiplicity_pos`（多項式性と次元定理からの導出）。
- 未証明：`exists_isSamuelPoly`（Hilbert の定理）、`natDegree_poly_eq_dim`（次元定理）。
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

/-- **Hilbert–Samuel の定理**：`I = (x₁, …, x_s)` が `m_D` 準素で `M` が有限生成なら、Samuel 関数は
十分大きい `n` で次数 `≤ s` の多項式の値に等しい。`gr_I(M)` が `(D/I)[X₁, …, X_s]` 上有限生成な
次数つき加群であることと、Hilbert の定理（Poincaré 級数が `p(X)/(1−X)^s`）による
（Atiyah–Macdonald Prop. 11.4、Thm 11.1）。 -/
theorem exists_isSamuelPoly (I : Ideal D) (hI : I.radical = maximalIdeal D)
    {s : ℕ} (x : Fin s → D) (hx : I = Ideal.span (Set.range x))
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M] :
    ∃ P : ℚ[X], IsSamuelPoly D I M P ∧ P.natDegree ≤ s := by
  sorry

/-- イデアル自体の冪について `e(I^v, M) = v^(dim M) e(I, M)`。
多項式性と定義から従い、次元定理は不要。
パラメータの成分ごとの冪の公式とは区別する。 -/
theorem multiplicity_pow
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M]
    (I : Ideal D) (hI : I.radical = maximalIdeal D) (v : ℕ) (hv : 0 < v) :
    multiplicity D (I ^ v) M =
      (v : ℚ) ^ dimToNat (Module.supportDim D M) * multiplicity D I M := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly D I hI x hx.symm M
  have hpoly := isSamuelPoly_poly D ⟨P, hP⟩
  have heq := poly_eq D (IsSamuelPoly.pow D M hpoly v hv)
  dsimp only [multiplicity]
  rw [heq, comp_C_mul_X_coeff]
  ring

/-- **次元定理**：`I` が `m_D` 準素なら `D` 自身の Samuel 多項式の次数は `dim D`
（Atiyah–Macdonald Thm 11.14、`d(D) = dim D` の部分）。 -/
theorem natDegree_poly_eq_dim (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    (poly D I D).natDegree = dimToNat (ringKrullDim D) := by
  sorry

/-- **正値性**：`I` が `m_D` 準素なら `0 < e(I, D)`。Samuel 多項式の次数が `dim D` で、
十分大きな正の整数で正値をとる多項式の最高次係数は正だから。 -/
theorem multiplicity_pos (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    0 < multiplicity D I D := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly D I hI x hx.symm D
  have hp := isSamuelPoly_poly D ⟨P, hP⟩
  dsimp only [multiplicity]
  rw [Module.supportDim_self_eq_ringKrullDim, ← natDegree_poly_eq_dim D I hI,
    coeff_natDegree]
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (IsSamuelPoly.leadingCoeff_pos D hI hp)

/-- パラメータ系 `z` について `0 < e((z), D)`（`multiplicity_pos` の特別な場合）。 -/
theorem multiplicity_pos_of_isSystemOfParameters {h : ℕ} (z : Fin h → D)
    (hz : IsSystemOfParameters D z) :
    0 < multiplicity D (Ideal.span (Set.range z)) D :=
  multiplicity_pos D _ hz.2

end statements

end HilbertSamuel

end SerrePositivity
