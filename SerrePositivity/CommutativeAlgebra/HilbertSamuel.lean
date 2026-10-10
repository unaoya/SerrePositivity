module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import Mathlib.Algebra.Polynomial.Roots
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

定義は標準のものを採り、Samuel 関数の多項式性（Hilbert の定理）、次元定理（`deg P = dim D`）、
正値性は主張だけ書いて `sorry` とする。これらは Mathlib にない可換環論の一般論で、
`notes/section-2-plan.md` §5 のとおり別トラックで証明する。多項式の一意性と、存在から定義の
`poly` が実際に Samuel 関数を表すことは、ここで証明する。

以前 `CommutativeAlgebra/Multiplicity.lean` にあった極限の式による定義（極限の存在を仮定しない
junk value つきのもの）は、2026-10-10 にこの定義に置き換えて削除した。

## 内容

- `samuelFunction`、`IsSamuelPoly`、`IsSamuelPoly.unique`、`poly`、`isSamuelPoly_poly`。
- `multiplicity` の定義。
- 主張（`sorry`）：`samuelFunction_ne_top`（有限性）、`exists_isSamuelPoly`（Hilbert の定理）、
  `natDegree_poly_eq_dim`（次元定理）、`multiplicity_pos`（正値性）。
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

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

/-- **Hilbert–Samuel 重複度** `e(I, M) := d! · (poly I M).coeff d`、`d = dim M`。
`M = D`、`I` が `m_D` 準素なら、`poly` の次数は `dim D` なので最高次係数の `d!` 倍。 -/
noncomputable def multiplicity (I : Ideal D) (M : Type u) [AddCommGroup M] [Module D M] : ℚ :=
  let d := dimToNat (Module.supportDim D M)
  (d.factorial : ℚ) * (poly D I M).coeff d

/-! ## 主張（可換環論の一般論。証明は別トラック、当面 `sorry`） -/

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

/-- **Hilbert–Samuel の定理**：`I = (x₁, …, x_s)` が `m_D` 準素で `M` が有限生成なら、Samuel 関数は
十分大きい `n` で次数 `≤ s` の多項式の値に等しい。`gr_I(M)` が `(D/I)[X₁, …, X_s]` 上有限生成な
次数つき加群であることと、Hilbert の定理（Poincaré 級数が `p(X)/(1−X)^s`）による
（Atiyah–Macdonald Prop. 11.4、Thm 11.1）。 -/
theorem exists_isSamuelPoly (I : Ideal D) (hI : I.radical = maximalIdeal D)
    {s : ℕ} (x : Fin s → D) (hx : I = Ideal.span (Set.range x))
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M] :
    ∃ P : ℚ[X], IsSamuelPoly D I M P ∧ P.natDegree ≤ s := by
  sorry

/-- **次元定理**：`I` が `m_D` 準素なら `D` 自身の Samuel 多項式の次数は `dim D`
（Atiyah–Macdonald Thm 11.14、`d(D) = dim D` の部分）。 -/
theorem natDegree_poly_eq_dim (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    (poly D I D).natDegree = dimToNat (ringKrullDim D) := by
  sorry

/-- **正値性**：`I` が `m_D` 準素なら `0 < e(I, D)`。Samuel 多項式の次数が `dim D` で、
整数値をとる多項式の最高次係数は正だから。 -/
theorem multiplicity_pos (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    0 < multiplicity D I D := by
  sorry

/-- パラメータ系 `z` について `0 < e((z), D)`（`multiplicity_pos` の特別な場合）。 -/
theorem multiplicity_pos_of_isSystemOfParameters {h : ℕ} (z : Fin h → D)
    (hz : IsSystemOfParameters D z) :
    0 < multiplicity D (Ideal.span (Set.range z)) D :=
  multiplicity_pos D _ hz.2

end statements

end HilbertSamuel

end SerrePositivity
