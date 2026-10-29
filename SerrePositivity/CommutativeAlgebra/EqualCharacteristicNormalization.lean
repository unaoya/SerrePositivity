module

public import SerrePositivity.CommutativeAlgebra.CoefficientField
public import SerrePositivity.CommutativeAlgebra.PrimaryParameterExistence
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-! # 同標数の通常の有限正規化（Cohen の構造定理）

概要：次元 `h` の同標数 `p` の完備 Noether 局所環 `D` について、係数体 `φ : k = D/m → D` とパラメータ系 `z_1, …, z_h`
を取ると、評価 `k[[X_1, …, X_h]] → D`（`X_i ↦ z_i`）は単射かつ有限で、剰余体へ全射。したがって `D` は正則完備局所環
`k[[X]]` 上有限（Cohen の構造定理の同標数の場合、`exists_cohen_normalization_equalCharacteristic`）。
方針：係数体は p 基底の持ち上げ（`CoefficientField`）、パラメータ系は準素イデアル内の選択（`PrimaryParameterExistence`）。
有限性は閉ファイバー `D/(z)` の有限性から（`FiniteNormalization`）、単射性は次元の一致から。
規約：分数体の拡大の分離性は主張しない（それが Cohen–Gabber の内容）。
使われ方：Cohen–Gabber（`CohenGabber*`）と中間係数体上の次元計算（`CofiniteNormalization`）。
Mathlib への提出候補（mathlib-upstream）。
-/

@[expose] public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 指定係数と準素なパラメータの評価は有限写像を与える。標数の仮定は不要。 -/
theorem exists_finite_powerSeries_map_of_parameters
    {k D : Type u} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
    {σ : Type*} [Finite σ] (z : σ → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries σ k →+* D,
      F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
        (∀ a, F (MvPowerSeries.C a) = φ a) ∧ ∀ i, F (MvPowerSeries.X i) = z i := by
  let J := Ideal.span (Set.range z)
  have hJm : J ≤ maximalIdeal D := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzm i
  let : IsAdicComplete J D := isAdicComplete_finite_of_le_maximalIdeal J hJm
  let : Algebra k D := φ.toAlgebra
  let : Module.Finite k (D ⧸ J) := finite_quotient_of_common_residue_primary hφ J hprimary
  have hz (i : σ) : z i ∈ J := Ideal.subset_span (Set.mem_range_self i)
  let F := adicPowerSeriesEval (algebraMap k D) J z hz
  have hfinite : F.Finite := adicPowerSeriesEval_finite_of_span J z hz rfl
  have hC : ∀ a, F (MvPowerSeries.C a) = φ a := adicPowerSeriesEval_C _ J z hz
  have hX : ∀ i, F (MvPowerSeries.X i) = z i := adicPowerSeriesEval_X _ J z hz
  have hres : Function.Surjective ((residue D).comp F) := by
    intro a
    obtain ⟨r, hr⟩ := hφ a
    refine ⟨MvPowerSeries.C r, ?_⟩
    change residue D (F (MvPowerSeries.C r)) = a
    rw [hC]
    exact hr
  exact ⟨F, hfinite, hres, hC, hX⟩

/-- 指定した係数写像と h 個のパラメータから、単射かつ有限な評価を構成する。
終域の整域性は不要。h=0も同じ構成で扱う。 -/
theorem exists_injective_finite_powerSeries_map_of_parameters
    {k D : Type u} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
    {h : ℕ} (hdim : ringKrullDim D = h)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries (Fin h) k →+* D,
      Function.Injective F ∧ F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
        (∀ a, F (MvPowerSeries.C a) = φ a) ∧ ∀ i, F (MvPowerSeries.X i) = z i := by
  obtain ⟨F, hf, hres, hC, hX⟩ := exists_finite_powerSeries_map_of_parameters φ hφ z hzm hprimary
  have hA : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
    rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_eq_zero_of_field, zero_add]
  exact ⟨F, ringHom_injective_of_finite_of_equal_dimension F hf hA hdim, hf, hres, hC, hX⟩

/-- 次元 h の同標数完備Noether局所環に対する通常の有限正規化。
係数写像とパラメータと、それらを評価する同じ写像を供給する。分離性は含まない。 -/
theorem exists_equalCharacteristic_finite_normalization
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (φ : ResidueField D →+* D) (z : Fin h → D)
      (F : MvPowerSeries (Fin h) (ResidueField D) →+* D),
      (residue D).comp φ = RingHom.id (ResidueField D) ∧
        IsSystemOfParameters D z ∧ Function.Injective F ∧ F.Finite ∧
          Function.Surjective ((residue D).comp F) ∧
            (∀ a, F (MvPowerSeries.C a) = φ a) ∧ ∀ i, F (MvPowerSeries.X i) = z i := by
  obtain ⟨φ, _, _, hφ⟩ := exists_coefficientField_ringHom (A := D) p
  have hφsurj : Function.Surjective ((residue D).comp φ) := by
    rw [hφ]
    exact Function.surjective_id
  have he : dimToNat (ringKrullDim D) = h := by
    rw [hdim]
    simp [dimToNat]
  have hparams := PrimaryParameterExistence.exists_systemOfParameters_in_primary D
    (maximalIdeal D) (maximalIdeal.isMaximal D).isPrime.radical
  rw [he] at hparams
  obtain ⟨z, hzm, hz⟩ := hparams
  obtain ⟨F, hinj, hfin, hres, hC, hX⟩ :=
    exists_injective_finite_powerSeries_map_of_parameters φ hφsurj hdim z hzm hz.2
  exact ⟨φ, z, F, hφ, hz, hinj, hfin, hres, hC, hX⟩

/-- 通常のCohen正規化を、標準冪級数基底と正則性・完備性を含む形で供給する。
Cohen–Gabber の分数体拡大の分離性は別の証明課題。 -/
theorem exists_cohen_normalization_equalCharacteristic
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
        Function.Surjective ((residue D).comp (algebraMap A D)) ∧
          ∃ (t : Fin h → A) (e : A ≃+* MvPowerSeries (Fin h) (ResidueField D)),
            Ideal.span (Set.range t) = maximalIdeal A ∧ ∀ i, e (t i) = MvPowerSeries.X i := by
  obtain ⟨_, _, F, _, _, hinj, hfin, hres, _, _⟩ :=
    exists_equalCharacteristic_finite_normalization D hdim p
  let k := ResidueField D
  let A := MvPowerSeries (Fin h) k
  let : IsRegularLocalRing A := isRegularLocalRing_mvPowerSeries_fin k h
  let : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let : IsAdicComplete (maximalIdeal A) A := isAdicComplete_powerSeries_maximalIdeal (Fin h) k
  let : Algebra A D := F.toAlgebra
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hinj, hfin, hres, MvPowerSeries.X, RingEquiv.refl A, ?_, fun _ ↦ rfl⟩
  rw [powerSeries_maximalIdeal_eq, maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq]

end SerrePositivity
