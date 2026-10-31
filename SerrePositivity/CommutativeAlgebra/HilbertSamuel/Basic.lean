module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.PolynomialGrowth

/-! # Samuel 関数と重複度の基本

## 概要

局所環 `R`、イデアル `I`、加群 `M` について、Samuel 関数 `n ↦ ℓ(M / I^n M)`、それを十分先で表す多項式
（`IsSamuelPoly`、`poly`）、重複度 `multiplicity` を定義し、加群の長さに関する基本性質（正値性、
短完全列と全射での比較、環同型での不変性）を示す。

## 方針

Samuel 関数の多項式性は Hilbert 級数の有理性（`HilbertSamuel/Polynomial`）から。ここでは定義と、
長さの加法性から直接出る性質だけを扱う。

## 規約

名前空間は `HilbertSamuel`。CLMST が `HilbertSamuel.multiplicity` と `multiplicity_span_map_ringEquiv` を使うので名前を変えない。

## 使われ方

Hilbert–Samuel の理論全体、Koszul 重複度の公式（B2）、CLMST のパラメータの長さ。
-/

@[expose] public noncomputable section

universe u v w

section Basic

open Polynomial IsLocalRing Filter

namespace SerrePositivity

namespace HilbertSamuel

variable (D : Type u) [CommRing D]

/-- Samuel 関数 `n ↦ ℓ_D(M / I^n M)`。 -/
noncomputable def samuelFunction (I : Ideal D) (M : Type v) [AddCommGroup M] [Module D M]
    (n : ℕ) : ℕ∞ :=
  Module.length D (M ⧸ (I ^ n • ⊤ : Submodule D M))

/-- 多項式 `P ∈ ℚ[X]` が Samuel 関数を表すこと：十分大きい `n` で `ℓ(M/I^n M)` は有限で
`P(n)` に等しい。 -/
def IsSamuelPoly (I : Ideal D) (M : Type v) [AddCommGroup M] [Module D M] (P : ℚ[X]) : Prop :=
  ∀ᶠ n in Filter.atTop,
    samuelFunction D I M n ≠ ⊤ ∧ ((samuelFunction D I M n).toNat : ℚ) = P.eval (n : ℚ)

variable {D}

/-- Samuel 関数を表す多項式は一意（無限個の自然数で値が一致する）。 -/
lemma IsSamuelPoly.unique {I : Ideal D} {M : Type v} [AddCommGroup M] [Module D M]
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
noncomputable def poly (I : Ideal D) (M : Type v) [AddCommGroup M] [Module D M] : ℚ[X] :=
  if h : ∃ P : ℚ[X], IsSamuelPoly D I M P then h.choose else 0

/-- 表す多項式が存在すれば、`poly` がそれ。 -/
lemma isSamuelPoly_poly {I : Ideal D} {M : Type v} [AddCommGroup M] [Module D M]
    (h : ∃ P : ℚ[X], IsSamuelPoly D I M P) : IsSamuelPoly D I M (poly D I M) := by
  simp only [poly, h, dite_true]
  exact Exists.choose_spec _

/-- 表す多項式 `P` があれば `poly = P`。 -/
lemma poly_eq {I : Ideal D} {M : Type v} [AddCommGroup M] [Module D M] {P : ℚ[X]}
    (hP : IsSamuelPoly D I M P) : poly D I M = P :=
  (isSamuelPoly_poly D ⟨P, hP⟩).unique hP

section powers

variable (M : Type v) [AddCommGroup M] [Module D M]

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
noncomputable def multiplicity (I : Ideal D) (M : Type v) [AddCommGroup M] [Module D M] : ℚ :=
  let d := dimToNat (Module.supportDim D M)
  (d.factorial : ℚ) * (poly D I M).coeff d

/-! ## Samuel 関数の性質と、多項式性・次元定理の未証明箇所 -/

section statements

variable [IsNoetherianRing D] [IsLocalRing D]

/-- **有限性**：`I` が `m_D` 準素（`√I = m_D`）で `M` が有限生成なら `ℓ(M/I^n M) < ∞`。
`M/I^n M` は `I^n` で消える有限生成加群で、`D/I` は Artin 環なので有限長
（`isFiniteLength_of_le_radical_annihilator`）。 -/
theorem samuelFunction_ne_top (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (M : Type v) [AddCommGroup M] [Module D M] [Module.Finite D M] (n : ℕ) :
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
  exact leadingCoeff_pos_of_eventually_eval_pos hpos

end statements

end HilbertSamuel

end SerrePositivity

end Basic

section Modules

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable {R : Type u} {M N : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An `R`-linear equivalence identifies the quotients by every ideal power. -/
noncomputable def samuelQuotientEquiv (I : Ideal R) (e : M ≃ₗ[R] N) (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

/-- Samuel functions depend only on the isomorphism class of the module. -/
lemma samuelFunction_eq_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N) (n : ℕ) :
    samuelFunction R I M n = samuelFunction R I N n :=
  (samuelQuotientEquiv I e n).length_eq

/-- A Samuel polynomial remains a Samuel polynomial after a linear equivalence. -/
lemma IsSamuelPoly.of_linearEquiv {I : Ideal R} {P : ℚ[X]}
    (hP : IsSamuelPoly R I M P) (e : M ≃ₗ[R] N) : IsSamuelPoly R I N P := by
  simpa only [IsSamuelPoly, ← samuelFunction_eq_of_linearEquiv I e] using hP

section localModules

variable [IsLocalRing R] [Module.Finite R M] [Nontrivial M]

/-- Nakayama: a proper ideal power cannot generate a nonzero finite module. -/
lemma pow_smul_top_ne_top (I : Ideal R) (hI : I.radical = maximalIdeal R)
    {n : ℕ} (hn : 0 < n) : (I ^ n • ⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  have hrad : I ^ n ≤ Ideal.jacobson (⊥ : Ideal R) :=
    ((Ideal.pow_le_self hn.ne').trans (Ideal.le_radical.trans_eq hI)).trans
      (maximalIdeal_le_jacobson _)
  have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I ^ n)
    (⊤ : Submodule R M) Module.Finite.fg_top (by rw [h]) hrad
  exact top_ne_bot hz

/-- Positive powers give nonzero quotients, so the Samuel function is positive. -/
lemma samuelFunction_pos_of_nontrivial (I : Ideal R)
    (hI : I.radical = maximalIdeal R) {n : ℕ} (hn : 0 < n) :
    0 < samuelFunction R I M n := by
  let : Nontrivial (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr (pow_smul_top_ne_top (M := M) I hI hn)
  exact Module.length_pos

/-- The leading coefficient of the Samuel polynomial of a finite nonzero
module is positive. The existence and dimension theorems are not used. -/
lemma IsSamuelPoly.leadingCoeff_pos_of_nontrivial {I : Ideal R} {P : ℚ[X]}
    (hI : I.radical = maximalIdeal R) (hP : IsSamuelPoly R I M P) :
    0 < P.leadingCoeff := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ) := by
    filter_upwards [hP, eventually_gt_atTop 0] with n hn hnpos
    rw [← hn.2]
    exact Nat.cast_pos.mpr (ENat.toNat_pos
      (samuelFunction_pos_of_nontrivial (M := M) I hI hnpos).ne' hn.1)
  exact leadingCoeff_pos_of_eventually_eval_pos hpos

end localModules

end SerrePositivity.HilbertSamuel

end Modules

section Surjection

open scoped Pointwise

namespace SerrePositivity.HilbertSamuel

variable {R : Type u} {M N : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjection induces a map on every Samuel quotient. -/
def samuelQuotientMap (I : Ideal R) (f : M →ₗ[R] N) (n : ℕ) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top (I ^ n) f)

/-- The map on Samuel quotients is surjective when the original map is. -/
lemma samuelQuotientMap_surjective (I : Ideal R) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (samuelQuotientMap I f n) := by
  intro y
  obtain ⟨y, rfl⟩ := (I ^ n • ⊤ : Submodule R N).mkQ_surjective y
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- Surjections decrease Samuel functions, without any finiteness hypotheses. -/
lemma samuelFunction_le_of_surjective (I : Ideal R) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (n : ℕ) :
    samuelFunction R I N n ≤ samuelFunction R I M n :=
  Module.length_le_of_surjective (samuelQuotientMap I f n)
    (samuelQuotientMap_surjective I f hf n)

/-- If `p ≤ q` and `x ∈ q`, the canonical map `R/p → R/q` kills `x(R/p)`. -/
lemma pointwise_smul_top_le_ker_factor (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) :
    (x • ⊤ : Submodule R (R ⧸ p)) ≤ LinearMap.ker (Submodule.factor hpq) := by
  rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
  intro y _
  obtain ⟨r, rfl⟩ := p.mkQ_surjective y
  change (Submodule.Quotient.mk (x * r) : R ⧸ q) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact q.mul_mem_right r hx

/-- The canonical surjection after quotienting by a scalar that belongs to `q`. -/
def quotSMulTopToIdealQuotient (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) : QuotSMulTop x (R ⧸ p) →ₗ[R] R ⧸ q :=
  (x • ⊤ : Submodule R (R ⧸ p)).liftQ (Submodule.factor hpq)
    (pointwise_smul_top_le_ker_factor p q hpq x hx)

/-- This canonical map is surjective. -/
lemma quotSMulTopToIdealQuotient_surjective (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) :
    Function.Surjective (quotSMulTopToIdealQuotient p q hpq x hx) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.factor_surjective hpq y
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- The Samuel growth of `R/q` is bounded by that of `(R/p)/x(R/p)`. -/
lemma samuelFunction_idealQuotient_le_quotSMulTop (I p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) (n : ℕ) :
    samuelFunction R I (R ⧸ q) n ≤
      samuelFunction R I (QuotSMulTop x (R ⧸ p)) n :=
  samuelFunction_le_of_surjective I (quotSMulTopToIdealQuotient p q hpq x hx)
    (quotSMulTopToIdealQuotient_surjective p q hpq x hx) n

end SerrePositivity.HilbertSamuel

end Surjection

section RingEquiv

namespace SerrePositivity.HilbertSamuel

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 環同型に対応するイデアルの商の、基底環に関する加群長は等しい。 -/
theorem length_quotient_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    Module.length S (S ⧸ I.map e.toRingHom) = Module.length R (R ⧸ I) :=
  (length_quotient_eq_of_equiv R S e e (fun _ => rfl) I).symm

/-- 環自体の Samuel 関数は環同型とイデアルの像によって変わらない。 -/
theorem samuelFunction_map_ringEquiv (e : R ≃+* S) (I : Ideal R) (n : ℕ) :
    samuelFunction S (I.map e.toRingHom) S n = samuelFunction R I R n := by
  have hR : (I ^ n • ⊤ : Submodule R R) = I ^ n :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  have hS : ((I.map e.toRingHom) ^ n • ⊤ : Submodule S S) = (I.map e.toRingHom) ^ n :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  unfold samuelFunction
  rw [hR, hS, ← Ideal.map_pow]
  exact length_quotient_map_ringEquiv e (I ^ n)

/-- 環自体の Samuel 多項式である条件は、環同型に沿ってイデアルを移しても同じ。 -/
theorem isSamuelPoly_map_ringEquiv_iff (e : R ≃+* S) (I : Ideal R) (P : Polynomial ℚ) :
    IsSamuelPoly S (I.map e.toRingHom) S P ↔ IsSamuelPoly R I R P := by
  simp only [IsSamuelPoly, samuelFunction_map_ringEquiv]

/-- 選択した Samuel 多項式は環同型で変わらない。存在しない場合も両側で零となる。 -/
theorem poly_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    poly S (I.map e.toRingHom) S = poly R I R := by
  classical
  by_cases h : ∃ P : Polynomial ℚ, IsSamuelPoly R I R P
  · exact poly_eq S ((isSamuelPoly_map_ringEquiv_iff e I _).mpr (isSamuelPoly_poly R h))
  · have hS : ¬ ∃ P : Polynomial ℚ, IsSamuelPoly S (I.map e.toRingHom) S P := by
      rintro ⟨P, hP⟩
      exact h ⟨P, (isSamuelPoly_map_ringEquiv_iff e I P).mp hP⟩
    simp only [poly, h, hS, dite_false]

/-- 環自体の Hilbert–Samuel 重複度は、環同型と対応するイデアルについて一致する。 -/
theorem multiplicity_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    multiplicity S (I.map e.toRingHom) S = multiplicity R I R := by
  simp only [multiplicity, Module.supportDim_self_eq_ringKrullDim]
  rw [← ringKrullDim_eq_of_ringEquiv e, poly_map_ringEquiv]

/-- 生成元の族を環同型で移したイデアルについて、環自体の重複度は一致する。 -/
theorem multiplicity_span_map_ringEquiv (e : R ≃+* S) {ι : Type*} (x : ι → R) :
    multiplicity S (Ideal.span (Set.range (e ∘ x))) S =
      multiplicity R (Ideal.span (Set.range x)) R := by
  rw [Set.range_comp, ← Ideal.map_span]
  exact multiplicity_map_ringEquiv e (Ideal.span (Set.range x))

end SerrePositivity.HilbertSamuel

end RingEquiv
