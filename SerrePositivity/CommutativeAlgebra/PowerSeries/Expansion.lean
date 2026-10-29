module

public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # 冪級数環の有限な拡大と基底

概要：`K` が `E` 上の有限基底 `B` を持ち `q > 0` のとき、係数拡大と `X_i ↦ T_i^q` による
`E[[X]] → K[[T]]` は有限自由で、基底は `T^r · B a`（`r_i < q`）。
- 指数を `q` で割った商と余りで、冪級数は `Σ_r T^r · (余り r の成分の q 乗展開)` と一意に分かれる。
- 完全標数 `p` の係数では、`p^n` 乗展開は係数の逆 Frobenius の `p^n` 乗になり、`p^n` 乗と変数を像に含む射は全射。
方針：基底は二段に分ける。`K[[X]]` の `E[[X]]` 上の基底 `C (B a)`（Mathlib の係数写像による代数構造）と、
`X ↦ X^q` による `K[[X]]` 自身の上の基底 `X^r` を、Mathlib の `Basis.smulTower'` で合成する。
規約：`X ↦ X^q` の作用は自己作用と区別するため `powerSeriesExpandModule` として明示的に渡す。
使われ方：中間係数体に沿う冪級数の有限拡大（`CofinitePowerSeriesExpansion`）、分数体の基底（`PowerSeries/FractionField`）、
根の塔の mod p 全射性。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Residue

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- 有限個の剰余から指数を作る。 -/
def powerSeriesResidueExponent (q : ℕ) (e : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ))

@[simp] theorem powerSeriesResidueExponent_apply (q : ℕ) (e : σ → Fin q) (i : σ) :
    powerSeriesResidueExponent q e i = (e i : ℕ) := rfl

/-- 指数の各成分の剰余。 -/
def powerSeriesResidueIndex (q : ℕ) (hq : 0 < q) (d : σ →₀ ℕ) : σ → Fin q :=
  fun i ↦ ⟨d i % q, Nat.mod_lt _ hq⟩

/-- 指数の各成分の商。 -/
def powerSeriesQuotientExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun a ↦ a / q) (Nat.zero_div q)

/-- 一つの剰余類に属する係数を集めた冪級数。 -/
def powerSeriesResidueComponent (q : ℕ) (e : σ → Fin q)
    (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ MvPowerSeries.coeff (q • d + powerSeriesResidueExponent q e) φ

theorem powerSeries_exponent_division (q : ℕ) (hq : 0 < q) (d : σ →₀ ℕ) :
    q • powerSeriesQuotientExponent q d +
      powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    powerSeriesQuotientExponent, Finsupp.mapRange_apply,
    powerSeriesResidueExponent_apply, powerSeriesResidueIndex]
  exact Nat.div_add_mod (d i) q

/-- 剰余単項式と指数展開の係数。入力は任意の冪級数。 -/
theorem coeff_powerSeriesResidueExpansion (q : ℕ) (hq : 0 < q) (e : σ → Fin q)
    (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.monomial (powerSeriesResidueExponent q e) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq) φ) =
      if e = powerSeriesResidueIndex q hq d then
        MvPowerSeries.coeff (powerSeriesQuotientExponent q d) φ else 0 := by
  classical
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases he : e = powerSeriesResidueIndex q hq d
  · subst e
    have hdiv := powerSeries_exponent_division q hq d
    have hle : powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) ≤ d := by
      calc
        _ ≤ q • powerSeriesQuotientExponent q d +
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) :=
          le_add_of_nonneg_left zero_le
        _ = d := hdiv
    have hsub : d - powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) =
        q • powerSeriesQuotientExponent q d := by
      calc
        _ = (q • powerSeriesQuotientExponent q d +
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d)) -
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) :=
          congrArg (fun x ↦ x - powerSeriesResidueExponent q
            (powerSeriesResidueIndex q hq d)) hdiv.symm
        _ = _ := add_tsub_cancel_right _ _
    rw [ite_eq_left hle, hsub, MvPowerSeries.coeff_expand_smul, ite_eq_left rfl, one_mul]
  · rw [ite_eq_right he]
    split_ifs with hle
    · obtain ⟨i, hi⟩ : ∃ i, e i ≠ powerSeriesResidueIndex q hq d i := by
        by_contra! h
        exact he (funext h)
      have hnot : ¬ q ∣ (d - powerSeriesResidueExponent q e) i := by
        intro hdvd
        have hli : (e i : ℕ) ≤ d i := hle i
        have hm := Nat.mod_eq_zero_of_dvd hdvd
        have hi' : (e i : ℕ) ≠ d i % q := by
          intro h
          apply hi
          exact Fin.ext h
        simp only [Finsupp.tsub_apply, powerSeriesResidueExponent_apply] at hm
        have hemod := Nat.mod_eq_of_lt (e i).isLt
        have hsum := Nat.add_mod (d i - (e i : ℕ)) (e i : ℕ) q
        rw [Nat.sub_add_cancel hli, hm, hemod, zero_add, hemod] at hsum
        exact hi' hsum.symm
      rw [MvPowerSeries.coeff_expand_of_not_dvd q (Nat.ne_of_gt hq) _ hnot, mul_zero]
    · rfl


theorem coeff_powerSeriesResidueTerm (q : ℕ) (hq : 0 < q) (e : σ → Fin q)
    (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.monomial (powerSeriesResidueExponent q e) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q e φ)) =
      if e = powerSeriesResidueIndex q hq d then MvPowerSeries.coeff d φ else 0 := by
  classical
  rw [coeff_powerSeriesResidueExpansion q hq]
  split_ifs with he
  · subst e
    change MvPowerSeries.coeff
      (q • powerSeriesQuotientExponent q d +
        powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d)) φ = _
    rw [powerSeries_exponent_division]
  · rfl

/-- 剰余と商から組み立てた指数の剰余を抽出する。 -/
@[simp] theorem powerSeriesResidueIndex_scale_add (q : ℕ) (hq : 0 < q)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    powerSeriesResidueIndex q hq (q • d + powerSeriesResidueExponent q r) = r := by
  funext i
  apply Fin.ext
  change (q * d i + (r i : ℕ)) % q = (r i : ℕ)
  simp [Nat.add_mod, Nat.mod_eq_of_lt (r i).isLt]

/-- 剰余と商から組み立てた指数の商を抽出する。 -/
@[simp] theorem powerSeriesQuotientExponent_scale_add (q : ℕ) (hq : 0 < q)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    powerSeriesQuotientExponent q (q • d + powerSeriesResidueExponent q r) = d := by
  ext i
  change (q * d i + (r i : ℕ)) / q = d i
  rw [Nat.mul_add_div hq, Nat.div_eq_of_lt (r i).isLt, add_zero]

open Classical in
/-- 冪級数の指数剰余分解。係数環の完全性はまだ必要ない。 -/
theorem powerSeries_residue_decomposition (q : ℕ) (hq : 0 < q)
    (φ : MvPowerSeries σ R) :
    φ = ∑ e : σ → Fin q,
      MvPowerSeries.monomial (powerSeriesResidueExponent q e) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q e φ) := by
  classical
  ext d
  simp only [map_sum, coeff_powerSeriesResidueTerm q hq]
  simp

omit [Fintype σ] in
/-- 完全係数環上では、変数の指数の展開は係数の逆 Frobenius の p^n 乗になる。 -/
theorem powerSeries_expand_eq_frobeniusRoot_pow (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (n : ℕ) (φ : MvPowerSeries σ R) :
    MvPowerSeries.expand (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) φ =
      (MvPowerSeries.map (iterateFrobeniusEquiv R p n).symm.toRingHom φ) ^ (p ^ n) := by
  rw [← MvPowerSeries.map_iterateFrobenius_expand p (Fact.out : p.Prime).ne_zero,
    MvPowerSeries.map_expand]
  congr 1
  ext d
  simp only [MvPowerSeries.coeff_map]
  exact ((iterateFrobeniusEquiv R p n).apply_symm_apply _).symm

open Classical in
/-- 任意の有限変数冪級数は、剰余単項式と p^n 乗の有限和として表せる。 -/
theorem powerSeries_exists_monomial_frobenius_decomposition (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (n : ℕ) (φ : MvPowerSeries σ R) :
    ∃ ψ : (σ → Fin (p ^ n)) → MvPowerSeries σ R,
      φ = ∑ e : σ → Fin (p ^ n),
        MvPowerSeries.monomial (powerSeriesResidueExponent (p ^ n) e) 1 * ψ e ^ (p ^ n) := by
  refine ⟨fun e ↦ MvPowerSeries.map (iterateFrobeniusEquiv R p n).symm.toRingHom
    (powerSeriesResidueComponent (p ^ n) e φ), ?_⟩
  calc
    φ = ∑ e : σ → Fin (p ^ n),
        MvPowerSeries.monomial (powerSeriesResidueExponent (p ^ n) e) 1 *
          MvPowerSeries.expand (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
            (powerSeriesResidueComponent (p ^ n) e φ) :=
      powerSeries_residue_decomposition (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) φ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [powerSeries_expand_eq_frobeniusRoot_pow]

omit [Fintype σ] in
/-- p^n 乗とすべての変数を像に含む射は、完全係数の有限変数冪級数環へ全射。 -/
theorem powerSeries_surjective_of_powers_and_variables {S : Type*} [CommRing S]
    [Finite σ]
    (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] (n : ℕ)
    (f : S →+* MvPowerSeries σ R)
    (hpow : ∀ φ : MvPowerSeries σ R, φ ^ (p ^ n) ∈ f.range)
    (hX : ∀ i : σ, MvPowerSeries.X i ∈ f.range) : Function.Surjective f := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  intro φ
  obtain ⟨ψ, hψ⟩ := powerSeries_exists_monomial_frobenius_decomposition p n φ
  change φ ∈ f.range
  rw [hψ]
  apply Subring.sum_mem
  intro e _
  apply Subring.mul_mem
  · rw [MvPowerSeries.monomial_one_eq, Finsupp.prod]
    apply Subring.prod_mem
    intro i _
    exact Subring.pow_mem _ (hX i) _
  · exact hpow (ψ e)

end Residue

section Expansion

open MvPowerSeries

variable {E K σ α : Type*} [CommRing E] [CommRing K] [Algebra E K]


/-- 各係数の指定基底に関する座標を集めた冪級数。 -/
def powerSeriesCoefficientComponent (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) (a : α) : MvPowerSeries σ E :=
  fun d ↦ B.repr (MvPowerSeries.coeff d f) a

@[simp] theorem coeff_powerSeriesCoefficientComponent (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) (a : α) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (powerSeriesCoefficientComponent B f a) =
      B.repr (MvPowerSeries.coeff d f) a := rfl

/-- 有限な係数基底の展開を、そのまま冪級数へ持ち上げる。 -/
theorem powerSeries_coefficient_decomposition [Fintype α] (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) :
    f = ∑ a, MvPowerSeries.C (B a) *
      MvPowerSeries.map (algebraMap E K) (powerSeriesCoefficientComponent B f a) := by
  ext d
  simpa only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
    coeff_powerSeriesCoefficientComponent, Algebra.smul_def, mul_comm] using
    (B.sum_repr (MvPowerSeries.coeff d f)).symm



/-- 係数の写像と変数のq乗による冪級数環の写像。 -/
def powerSeriesExpandMap (q : ℕ) (hq : 0 < q) :
    MvPowerSeries σ E →+* MvPowerSeries σ K :=
  (MvPowerSeries.expand q (Nat.ne_of_gt hq)).toRingHom.comp
    (MvPowerSeries.map (algebraMap E K))

/-- 変数のq乗による写像に沿う加群作用。同じ環の自己作用とも区別する。 -/
@[instance_reducible] def powerSeriesExpansionModule (q : ℕ) (hq : 0 < q) :
    Module (MvPowerSeries σ E) (MvPowerSeries σ K) :=
  @Algebra.toModule _ _ _ _ (powerSeriesExpandMap q hq).toAlgebra

@[simp] theorem powerSeriesExpandMap_C (q : ℕ) (hq : 0 < q) (a : E) :
    powerSeriesExpandMap (σ := σ) (K := K) q hq (MvPowerSeries.C a) =
      MvPowerSeries.C (algebraMap E K a) := by
  simp [powerSeriesExpandMap, MvPowerSeries.expand_C]

@[simp] theorem powerSeriesExpandMap_X (q : ℕ) (hq : 0 < q) (i : σ) :
    powerSeriesExpandMap (E := E) (K := K) q hq (MvPowerSeries.X i) =
      MvPowerSeries.X i ^ q := by
  simp [powerSeriesExpandMap, MvPowerSeries.expand_X]

/-- 係数写像が単射なら、変数の正の冪による写像も単射。変数の有限性は不要。 -/
theorem powerSeriesExpandMap_injective (q : ℕ) (hq : 0 < q)
    (hEK : Function.Injective (algebraMap E K)) :
    Function.Injective (powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq) := by
  intro f g hfg
  ext d
  apply hEK
  have h := congrArg (MvPowerSeries.coeff (q • d)) hfg
  change MvPowerSeries.coeff (q • d)
      (MvPowerSeries.expand q (Nat.ne_of_gt hq) (MvPowerSeries.map (algebraMap E K) f)) =
    MvPowerSeries.coeff (q • d)
      (MvPowerSeries.expand q (Nat.ne_of_gt hq) (MvPowerSeries.map (algebraMap E K) g)) at h
  simpa only [MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map] using h

open Classical in
/-- 係数の基底と変数の剰余単項式から、実際の有限和を構成する。 -/
theorem powerSeries_coefficient_residue_decomposition [Fintype σ] [Fintype α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) (f : MvPowerSeries σ K) :
    f = ∑ r : σ → Fin q, ∑ a : α,
      MvPowerSeries.monomial (powerSeriesResidueExponent q r) (B a) *
        powerSeriesExpandMap q hq
          (powerSeriesCoefficientComponent B (powerSeriesResidueComponent q r f) a) := by
  trans ∑ r : σ → Fin q,
    MvPowerSeries.monomial (powerSeriesResidueExponent q r) 1 *
      MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q r f)
  · exact powerSeries_residue_decomposition q hq f
  apply Finset.sum_congr rfl
  intro r _
  conv_lhs => rw [powerSeries_coefficient_decomposition B (powerSeriesResidueComponent q r f)]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, MvPowerSeries.expand_C, ← mul_assoc]
  change (MvPowerSeries.monomial _ 1 * MvPowerSeries.monomial 0 (B a)) * _ = _
  rw [MvPowerSeries.monomial_mul_monomial, add_zero, one_mul]
  rfl


/-- 係数基底 `B` の定数は、係数を拡大した冪級数環で独立。 -/
theorem powerSeriesCoefficientBasis_li [Finite α] (B : Module.Basis α E K) :
    LinearIndependent (MvPowerSeries σ E) (fun a ↦ (C (B a) : MvPowerSeries σ K)) := by
  classical
  let := Fintype.ofFinite α
  refine Fintype.linearIndependent_iff.mpr fun g hg a ↦ ?_
  ext d
  have h := congrArg (coeff d) hg
  simp only [Algebra.smul_def, MvPowerSeries.algebraMap_apply'', map_sum, coeff_mul_C,
    coeff_map, map_zero] at h
  have := Fintype.linearIndependent_iff.mp B.linearIndependent (fun a ↦ coeff d (g a))
    (by simpa only [Algebra.smul_def, mul_comm] using h) a
  simpa using this

/-- `K[[X]]` の `E[[X]]` 上の基底 `C (B a)`。作用は Mathlib の係数写像による標準の代数構造。 -/
noncomputable def powerSeriesCoefficientBasis [Finite α] (B : Module.Basis α E K) :
    Module.Basis α (MvPowerSeries σ E) (MvPowerSeries σ K) :=
  let := Fintype.ofFinite α
  Module.Basis.mk (v := fun a ↦ C (B a)) (powerSeriesCoefficientBasis_li B) (by
    intro f _
    rw [powerSeries_coefficient_decomposition B f]
    refine Submodule.sum_mem _ fun a _ ↦ ?_
    have := Submodule.smul_mem _ (powerSeriesCoefficientComponent B f a)
      (Submodule.subset_span (R := MvPowerSeries σ E)
        (Set.mem_range_self (f := fun a ↦ (C (B a) : MvPowerSeries σ K)) a))
    simpa only [Algebra.smul_def, MvPowerSeries.algebraMap_apply'', mul_comm] using this)

/-- 変数の q 乗による自己作用。 -/
@[instance_reducible] noncomputable def powerSeriesExpandModule (q : ℕ) (hq : 0 < q) :
    Module (MvPowerSeries σ K) (MvPowerSeries σ K) :=
  @Algebra.toModule _ _ _ _ (MvPowerSeries.expand q (Nat.ne_of_gt hq)).toRingHom.toAlgebra

/-- `X ↦ X^q` による作用での、`K[[X]]` 自身の上の基底 `X^r`（`r_i < q`）。 -/
noncomputable def powerSeriesMonomialBasis [Fintype σ] (q : ℕ) (hq : 0 < q) :
    letI := powerSeriesExpandModule (σ := σ) (K := K) q hq
    Module.Basis (σ → Fin q) (MvPowerSeries σ K) (MvPowerSeries σ K) := by
  classical
  letI := powerSeriesExpandModule (σ := σ) (K := K) q hq
  refine Module.Basis.mk (v := fun r ↦ monomial (powerSeriesResidueExponent q r) 1) ?_ ?_
  · refine Fintype.linearIndependent_iff.mpr fun g hg r ↦ ?_
    ext d
    have h := congrArg (coeff (q • d + powerSeriesResidueExponent q r)) hg
    change coeff _ (∑ i, MvPowerSeries.expand q (Nat.ne_of_gt hq) (g i) *
      monomial (powerSeriesResidueExponent q i) 1) = coeff _ 0 at h
    simp only [map_sum, mul_comm (MvPowerSeries.expand q _ _),
      coeff_powerSeriesResidueExpansion q hq, powerSeriesResidueIndex_scale_add,
      powerSeriesQuotientExponent_scale_add q hq, map_zero] at h
    simpa using h
  · intro f _
    rw [powerSeries_residue_decomposition q hq f]
    refine Submodule.sum_mem _ fun r _ ↦ ?_
    have := Submodule.smul_mem _ (powerSeriesResidueComponent q r f)
      (Submodule.subset_span (Set.mem_range_self (f := fun r ↦
        (monomial (powerSeriesResidueExponent q r) 1 : MvPowerSeries σ K)) r))
    change MvPowerSeries.expand q (Nat.ne_of_gt hq) _ * _ ∈ _ at this
    rwa [mul_comm] at this

@[simp] theorem powerSeriesCoefficientBasis_apply [Finite α] (B : Module.Basis α E K) (a : α) :
    powerSeriesCoefficientBasis (σ := σ) B a = C (B a) := by
  simp [powerSeriesCoefficientBasis]

theorem powerSeriesMonomialBasis_apply [Fintype σ] (q : ℕ) (hq : 0 < q) (r : σ → Fin q) :
    powerSeriesMonomialBasis (K := K) q hq r = monomial (powerSeriesResidueExponent q r) 1 := by
  simp [powerSeriesMonomialBasis]

/-- 係数拡大と変数の `q` 乗の二段の作用は、合成の作用とスカラー塔をなす。 -/
theorem powerSeriesExpansion_isScalarTower (q : ℕ) (hq : 0 < q) :
    @IsScalarTower (MvPowerSeries σ E) (MvPowerSeries σ K) (MvPowerSeries σ K)
      Algebra.toSMul ((powerSeriesExpandModule (K := K) q hq).toSMul)
      (powerSeriesExpansionModule (E := E) q hq).toSMul :=
  @IsScalarTower.of_algebraMap_eq (MvPowerSeries σ E) (MvPowerSeries σ K) (MvPowerSeries σ K)
    _ _ _ _ (MvPowerSeries.expand q (Nat.ne_of_gt hq)).toRingHom.toAlgebra
    (powerSeriesExpandMap q hq).toAlgebra (fun _ ↦ rfl)

/-- `E[[X]] → K[[T]]`（係数拡大と `X_i ↦ T_i^q`）に沿う基底 `T^r · B a`。二段の基底を `smulTower'` で合成する。 -/
noncomputable def powerSeriesExpansionBasis [Fintype σ] [Finite α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    Module.Basis ((σ → Fin q) × α) (MvPowerSeries σ E) (MvPowerSeries σ K) :=
  @Module.Basis.smulTower' (MvPowerSeries σ E) (MvPowerSeries σ K) (MvPowerSeries σ K) _ _ _
    _ (powerSeriesExpandModule q hq) (powerSeriesExpansionModule q hq)
    (powerSeriesExpansion_isScalarTower q hq) _ _
    (powerSeriesCoefficientBasis B) (powerSeriesMonomialBasis q hq)

@[simp] theorem powerSeriesExpansionBasis_apply [Fintype σ] [Finite α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) (x : (σ → Fin q) × α) :
    powerSeriesExpansionBasis B q hq x =
      MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2) := by
  refine (@Module.Basis.smulTower'_apply (MvPowerSeries σ E) (MvPowerSeries σ K)
    (MvPowerSeries σ K) _ _ _ _ (powerSeriesExpandModule q hq) (powerSeriesExpansionModule q hq)
    (powerSeriesExpansion_isScalarTower q hq) _ _
    (powerSeriesCoefficientBasis B) (powerSeriesMonomialBasis q hq) x).trans ?_
  change MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesCoefficientBasis B x.2) *
    powerSeriesMonomialBasis q hq x.1 = _
  rw [powerSeriesCoefficientBasis_apply, powerSeriesMonomialBasis_apply, MvPowerSeries.expand_C,
    mul_comm]
  change MvPowerSeries.monomial _ 1 * MvPowerSeries.monomial 0 (B x.2) = _
  rw [MvPowerSeries.monomial_mul_monomial, add_zero, one_mul]

/-- 非零係数環では、基底の添字から自由加群の階数を正確に計算する。 -/
theorem powerSeriesExpansion_finrank [Fintype σ] [Finite α] [Nontrivial E]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    Module.finrank (MvPowerSeries σ E) (MvPowerSeries σ K) =
      q ^ Fintype.card σ * Nat.card α := by
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) := (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  classical
  let : Fintype α := Fintype.ofFinite α
  rw [Module.finrank_eq_card_basis (powerSeriesExpansionBasis B q hq)]
  simp [Nat.card_eq_fintype_card]

/-- 有限係数基底と有限変数から、`E[[X]] → K[[T]]` の有限性。 -/
theorem powerSeriesExpandMap_finite [Finite σ] [Finite α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    (powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq).Finite := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) := (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  exact Module.Finite.of_basis (powerSeriesExpansionBasis B q hq)

end Expansion

end SerrePositivity
