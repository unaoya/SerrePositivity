module

public import SerrePositivity.HomologicalAlgebra.KoszulTorLength
public import SerrePositivity.HomologicalAlgebra.TorFiniteLengthBound
public import SerrePositivity.HomologicalAlgebra.TorUniformAnnihilator
public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Parameters
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization
public import SerrePositivity.CommutativeAlgebra.PerfectNilpotentLifting
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.Powers
public import Mathlib.RingTheory.KrullDimension.Field

/-! # パラメータの冪の Koszul ホモロジーの長さの増大

## 概要

`D` を完備 Noether 局所環で標数 `p`、剰余体は完全体、`h = dim D > 0` とする。
`D` のパラメータ系 `z` と `i > 0` について、定数 `C` があって全ての `q ≥ 1` で
`ℓ_D H_i(z^q; D) ≤ C q^{h-1}`。特に `ℓ_D H_i(z^{p^n}; D) / p^{nh} → 0`。

Roberts の Frobenius ホモロジー消滅定理（一般形の引用 `Inputs.frobenius_homology_length_tendsto_zero` は削除済み）を、
パラメータ Koszul 複体という特殊な場合に限って、Frobenius の性質を使わずに証明する。

## 方針

1. 係数体 `k → D` をとり、`R' = k[[Z]]` から `Z_j ↦ z_j` で評価すると `D` は有限 `R'` 加群
   （`exists_finite_powerSeries_parameters`）。
2. `Z^q` は `R'` の正則列なので、`ℓ_D H_i(z^q; D) = ℓ_{R'} Tor_i^{R'}(R'/(Z^q), D)`
   （`length_koszulHomologySelf_eq_length_torModule`）。
3. `q` によらない零でない `c ∈ R'` が `Tor_i(-, D)` を消し
   （`exists_ne_zero_smul_torModule_eq_zero`）、`D` の `q` によらない有限自由分解で
   `ℓ Tor_i(R'/(Z^q), D) ≤ β ℓ(R'/(c, Z^q))`（`length_torModule_le_of_smul_eq_zero`）。
4. `R'/(c)` は次元 `h - 1` なので `ℓ(R'/(c, Z^q)) ≤ C q^{h-1}`
   （`exists_length_quotient_generator_pow_le`）。

## 使われ方

`Paper/Section2/LengthAlgebra.lean` の `perfectClosure_length_properties` で、
Paper Theorem 2.5 の式 (2.4) の等標数部分に用いる、Roberts の引用に代わる高次 Koszul ホモロジーの消滅の入力。
-/

@[expose] public section

universe u

open IsLocalRing CategoryTheory Filter
open scoped ENNReal

namespace SerrePositivity

/-! ## 一般の補題 -/

section quotient

variable {R : Type u} [CommRing R]

/-- 巡回加群 `R/I` を `c` 倍の像で割った商は、`R/(I + (c))` と同じ長さ。 -/
lemma length_quotient_range_smul_eq (I : Ideal R) (c : R) :
    Module.length R ((R ⧸ I) ⧸ LinearMap.range (c • LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) =
      Module.length R (R ⧸ (I ⊔ Ideal.span {c})) := by
  have hrange : LinearMap.range (c • LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I)) =
      Submodule.map (Submodule.mkQ I) (Ideal.span {c} : Submodule R R) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I w
      refine ⟨c * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self c), ?_⟩
      simp only [Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      rfl
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.mkQ I a, ?_⟩
      simp only [Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm a c]
      rfl
  rw [hrange]
  exact (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {c})).length_eq

end quotient

/-! ## 冪級数環上の評価 -/

section powerSeries

variable (k : Type u) [Field k] (h : ℕ)

local notation "R'" => MvPowerSeries (Fin h) k

/-- 体係数の冪級数環の極大イデアルは変数で生成される。 -/
lemma mvPowerSeries_span_X_eq_maximalIdeal :
    Ideal.span (Set.range (MvPowerSeries.X : Fin h → R')) = maximalIdeal R' := by
  rw [powerSeries_maximalIdeal_eq, maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq]

/-- 体係数の冪級数環の次元は変数の個数。 -/
lemma ringKrullDim_mvPowerSeries_field : ringKrullDim R' = h := by
  rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_eq_zero_of_field, zero_add]

/-- 変数の正の冪は弱正則列で、その Koszul 複体は商の分解。 -/
lemma isKoszulResolution_mvPowerSeries_X_pow (q : ℕ) (hq : 0 < q) :
    IsKoszulResolution (fun j : Fin h ↦ (MvPowerSeries.X j : R') ^ q) := by
  let : IsRegularLocalRing R' := isRegularLocalRing_mvPowerSeries_fin k h
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal R' MvPowerSeries.X
    (mvPowerSeries_span_X_eq_maximalIdeal k h) (ringKrullDim_mvPowerSeries_field k h)
  have hm : ∀ x ∈ List.ofFn (MvPowerSeries.X : Fin h → R'), x ∈ maximalIdeal R' := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [← mvPowerSeries_span_X_eq_maximalIdeal k h]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hpow := isWeaklyRegular_map_pow R' hreg hm q hq
  rw [List.map_ofFn] at hpow
  exact isKoszulResolution_of_isWeaklyRegular _ hpow

/-- 零でない元 `c` を加えた変数の冪の商の長さは `C q^{h-1}` 以下。
`c` が単元なら商は零。そうでなければ次元 `h - 1` の環 `R'/(c)` で Samuel 関数の評価を使う。 -/
lemma exists_length_quotient_X_pow_sup_le (hh : 0 < h) (c : R') (hc : c ≠ 0) :
    ∃ C : ℕ, ∀ q : ℕ, 0 < q →
      Module.length R' (R' ⧸ (Ideal.span (Set.range fun j : Fin h ↦ (MvPowerSeries.X j : R') ^ q) ⊔
        Ideal.span {c})) ≤ ((C * q ^ (h - 1) : ℕ) : ℕ∞) := by
  let : IsRegularLocalRing R' := isRegularLocalRing_mvPowerSeries_fin k h
  let : IsDomain R' := isDomain_of_isRegularLocalRing R'
  by_cases hu : IsUnit c
  · refine ⟨0, fun q _ ↦ ?_⟩
    have htop : Ideal.span {c} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    rw [htop, sup_top_eq]
    have : Subsingleton (R' ⧸ (⊤ : Ideal R')) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact zero_le
  -- `E = R'/(c)` は次元 `h - 1` 以下の Noether 局所環
  set E := R' ⧸ Ideal.span {c}
  have hne : Ideal.span {c} ≠ ⊤ := fun h ↦ hu (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial E := Ideal.Quotient.nontrivial_iff.mpr hne
  let : IsLocalRing E :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdimE : dimToNat (ringKrullDim E) ≤ h - 1 := by
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hc)
    rw [ringKrullDim_mvPowerSeries_field k h] at h1
    have h2 := natCast_dimToNat_ringKrullDim E
    rw [← h2] at h1
    have h3 : ((dimToNat (ringKrullDim E) + 1 : ℕ) : WithBot ℕ∞) ≤ (h : WithBot ℕ∞) := by
      exact_mod_cast h1
    have h4 : dimToNat (ringKrullDim E) + 1 ≤ h := by exact_mod_cast h3
    omega
  let zbar : Fin h → E := fun j ↦ Ideal.Quotient.mk _ (MvPowerSeries.X j)
  have hspan : Ideal.span (Set.range zbar) = maximalIdeal E := by
    have hmap := map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective
    rw [← mvPowerSeries_span_X_eq_maximalIdeal k h, Ideal.map_span, ← Set.range_comp] at hmap
    exact hmap
  have hrad : (Ideal.span (Set.range zbar)).radical = maximalIdeal E := by
    rw [hspan]
    exact (maximalIdeal.isMaximal E).isPrime.radical
  obtain ⟨C, hC⟩ := exists_length_quotient_generator_pow_le E zbar hrad (h - 1) hdimE
  refine ⟨C, fun q hq ↦ ?_⟩
  -- `R'/((Z^q) + (c)) ≃ E/(z̄^q)`
  have hmapq : (Ideal.span (Set.range fun j : Fin h ↦ (MvPowerSeries.X j : R') ^ q)).map
      (Ideal.Quotient.mkₐ R' (Ideal.span {c})) =
        Ideal.span (Set.range fun j ↦ zbar j ^ q) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
  let e := DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span {c})
    (Ideal.span (Set.range fun j : Fin h ↦ (MvPowerSeries.X j : R') ^ q))
  rw [sup_comm, ← e.toLinearEquiv.length_eq, hmapq,
    Module.length_eq_of_surjective (R := E) Ideal.Quotient.mk_surjective]
  exact hC q hq

end powerSeries

/-! ## 係数体と有限な冪級数評価 -/

section coefficient

variable (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] (p : ℕ) [Fact p.Prime] [CharP D p]
  [CharP (ResidueField D) p] [PerfectField (ResidueField D)]

include p

/-- 完全剰余体を持つ標数 `p` の完備局所環のパラメータ系 `z` は、剰余体係数の冪級数環からの
有限な評価 `Z_j ↦ z_j` を与え、剰余体の上で全射。係数体は完全環からの一意な持ち上げで得る。 -/
theorem exists_finite_powerSeries_parameters {h : ℕ} (z : Fin h → D)
    (hz : IsSystemOfParameters D z) :
    ∃ F : MvPowerSeries (Fin h) (ResidueField D) →+* D,
      F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
        ∀ j, F (MvPowerSeries.X j) = z j := by
  let : CharP (D ⧸ maximalIdeal D) p := ‹CharP (ResidueField D) p›
  obtain ⟨l, hl, -⟩ := exists_unique_ringHom_lift_of_adicComplete p (maximalIdeal D)
    (RingHom.id (ResidueField D))
  let : Algebra (ResidueField D) D := l.toAlgebra
  set J := Ideal.span (Set.range z)
  have hJm : J ≤ maximalIdeal D := hz.2 ▸ Ideal.le_radical
  let : IsAdicComplete J D := isAdicComplete_finite_of_le_maximalIdeal (R := D) (M := D) J hJm
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    intro a
    exact ⟨a, RingHom.congr_fun hl a⟩
  let : Module.Finite (ResidueField D) (D ⧸ J) :=
    finite_quotient_of_common_residue_primary hres J hz.2
  have hx : ∀ i, z i ∈ J := fun i ↦ Ideal.subset_span ⟨i, rfl⟩
  refine ⟨adicPowerSeriesEval (algebraMap (ResidueField D) D) J z hx,
    adicPowerSeriesEval_finite_of_span J z hx rfl, fun a ↦ ⟨MvPowerSeries.C a, ?_⟩,
    adicPowerSeriesEval_X _ J z hx⟩
  change residue D (adicPowerSeriesEval (algebraMap (ResidueField D) D) J z hx
    (MvPowerSeries.C a)) = a
  rw [adicPowerSeriesEval_C]
  exact RingHom.congr_fun hl a

/-- **パラメータ Koszul 複体の高次ホモロジーの増大**：`i > 0` なら、定数 `C` があって
全ての `q ≥ 1` で `ℓ_D H_i(z^q; D) ≤ C q^{h-1}`。冪級数環上の Tor に移し、
一様な零化元と `q` によらない有限自由分解で評価する。 -/
theorem exists_length_koszulHomologySelf_pow_le {h : ℕ} (hh : 0 < h) (z : Fin h → D)
    (hz : IsSystemOfParameters D z) (i : ℕ) (hi : 0 < i) :
    ∃ C : ℕ, ∀ q : ℕ, 0 < q →
      Module.length D (koszulHomologySelf (fun j ↦ z j ^ q) i) ≤ ((C * q ^ (h - 1) : ℕ) : ℕ∞) := by
  set k := ResidueField D
  obtain ⟨F, hFfin, hFres, hFX⟩ := exists_finite_powerSeries_parameters D p z hz
  let : IsRegularLocalRing (MvPowerSeries (Fin h) k) := isRegularLocalRing_mvPowerSeries_fin k h
  let : IsDomain (MvPowerSeries (Fin h) k) := isDomain_of_isRegularLocalRing _
  let : Algebra (MvPowerSeries (Fin h) k) D := F.toAlgebra
  have : Module.Finite (MvPowerSeries (Fin h) k) D := hFfin
  -- `q` によらない零化元と有限自由分解
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_smul_torModule_eq_zero (R := MvPowerSeries (Fin h) k) D
  obtain ⟨G, ⟨hG⟩, -, hfree, hfin⟩ := regularResolution (MvPowerSeries (Fin h) k) D
  have := hfree (-(i : ℤ))
  have := hfin (-(i : ℤ))
  set β := Module.finrank (MvPowerSeries (Fin h) k) (G.X (-(i : ℤ)))
  let e := (Module.finBasis (MvPowerSeries (Fin h) k) (G.X (-(i : ℤ)))).equivFun
  obtain ⟨C₀, hC₀⟩ := exists_length_quotient_X_pow_sup_le k h hh c hc0
  refine ⟨β * C₀, fun q hq ↦ ?_⟩
  set W := MvPowerSeries (Fin h) k ⧸
    Ideal.span (Set.range fun j : Fin h ↦ (MvPowerSeries.X j : MvPowerSeries (Fin h) k) ^ q)
  have hK := isKoszulResolution_mvPowerSeries_X_pow k h q hq
  -- Koszul ホモロジーを Tor に移す
  have hcomp : (algebraMap (MvPowerSeries (Fin h) k) D ∘
      fun j : Fin h ↦ (MvPowerSeries.X j : MvPowerSeries (Fin h) k) ^ q) = fun j ↦ z j ^ q := by
    funext j
    change F (MvPowerSeries.X j ^ q) = z j ^ q
    rw [map_pow, hFX]
  have hlen := length_koszulHomologySelf_eq_length_torModule (T := D) hFres
    (fun j : Fin h ↦ (MvPowerSeries.X j : MvPowerSeries (Fin h) k) ^ q) hK i
  rw [hcomp] at hlen
  rw [hlen]
  -- `W` は有限長
  have hW : IsFiniteLength (MvPowerSeries (Fin h) k) W := by
    have hrad :
        (Ideal.span (Set.range (MvPowerSeries.X : Fin h → MvPowerSeries (Fin h) k))).radical =
          maximalIdeal _ := by
      rw [mvPowerSeries_span_X_eq_maximalIdeal]
      exact (maximalIdeal.isMaximal _).isPrime.radical
    obtain ⟨C', hC'⟩ := exists_length_quotient_generator_pow_le (MvPowerSeries (Fin h) k)
      MvPowerSeries.X hrad h (by
        rw [ringKrullDim_mvPowerSeries_field]
        simp [dimToNat])
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hC' q hq)
  -- 一様な零化元と有限自由分解による評価
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hbound := length_torModule_le_of_smul_eq_zero W D hW hG (i' + 1) β e c (hc W i')
  rw [length_quotient_range_smul_eq] at hbound
  refine hbound.trans ?_
  have h2 := hC₀ q hq
  calc
    β • Module.length (MvPowerSeries (Fin h) k) (MvPowerSeries (Fin h) k ⧸
        (Ideal.span (Set.range fun j : Fin h ↦ (MvPowerSeries.X j : MvPowerSeries (Fin h) k) ^ q) ⊔
          Ideal.span {c})) ≤ β • ((C₀ * q ^ (h - 1) : ℕ) : ℕ∞) := nsmul_le_nsmul_right h2 β
    _ = _ := by push_cast; ring

/-- 正規化した消滅：`i > 0` なら `ℓ_D H_i(z^{p^n}; D) / p^{nh} → 0`。
`exists_length_koszulHomologySelf_pow_le` の評価 `C p^{n(h-1)}` を `p^{nh}` で割る。 -/
theorem tendsto_length_koszulHomologySelf_frobenius_pow {h : ℕ} (hh : 0 < h) (z : Fin h → D)
    (hz : IsSystemOfParameters D z) (i : ℕ) (hi : 0 < i) :
    Tendsto (fun n : ℕ ↦
      (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞) /
        ((p ^ (n * h) : ℕ) : ℝ≥0∞)) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_length_koszulHomologySelf_pow_le D p hh z hz i hi
  have hp : (1 : ℝ≥0∞) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  -- 上界 `C (p⁻¹)^n` は零に収束する
  have hlim : Tendsto (fun n : ℕ ↦ (C : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ^ n) atTop (nhds 0) := by
    have h0 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (p : ℝ≥0∞)⁻¹)
      (ENNReal.inv_lt_one.mpr hp)
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.natCast_ne_top C))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) (fun n ↦ ?_)
  have hq : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hb := hC (p ^ n) hq
  have hden0 : ((p ^ (n * h) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos (n * h)).ne'
  have hdent : ((p ^ (n * h) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hden0 hdent]
  calc
    (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞)
        ≤ ((C * (p ^ n) ^ (h - 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hb
    _ = (C : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ^ n * ((p ^ (n * h) : ℕ) : ℝ≥0∞) := by
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      push_cast
      rw [← pow_mul, show n * (h' + 1) = n * h' + n by ring, pow_add,
        mul_assoc (C : ℝ≥0∞), ← mul_assoc ((p : ℝ≥0∞)⁻¹ ^ n), mul_comm ((p : ℝ≥0∞)⁻¹ ^ n),
        mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hp0 hpt, one_pow, mul_one]

end coefficient

end SerrePositivity
