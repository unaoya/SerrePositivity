module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Existence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import SerrePositivity.CommutativeAlgebra.Witt.PowerSeries
public import SerrePositivity.CommutativeAlgebra.Witt.CohenRing
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization

/-! # 混標数の Cohen 正規化

## 概要

剰余体 `k` が標数 `p` の完全体である、標数零の完備 Noether 局所整域 `D`（次元 `h > 0`）は、
`W(k)[[X_1, …, X_{h-1}]]` と同型な完備正則局所整域 `A` を部分環として含み、`D` は `A` 上有限で
剰余体は一致する。`A` の正則パラメータ系は `p` を先頭に、残りが変数 `X_i` に対応する
（`exists_cohen_normalization_mixedCharacteristic`）。

## 方針

`p` を先頭に置くパラメータ系をとり（`exists_mixedCharacteristic_systemOfParameters`。標数零の整域で
`p` は非零因子、剰余標数から極大イデアルに入る）、Witt 係数写像（`Witt/CohenRing`）と残りの
パラメータで冪級数評価を作る。閉ファイバーの有限性と基底の完備性から有限性が従う。

## 規約

完全剰余体の場合に限る。一般の剰余体は Cohen 環の構成が要る。

## 使われ方

Cohen 正規化の入力（`Inputs/CohenNormalization`）。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity

section Parameters

open IsLocalRing

/-- 次元h>0の混標数局所整域では、pを先頭とするh個のパラメータが存在する。
h=1では残りの列は空となり、(p)自体の根基が極大イデアルになる。 -/
theorem exists_mixedCharacteristic_systemOfParameters
    (D : Type*) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [CharZero D] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField D) p]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h) :
    ∃ z : Fin h → D, z ⟨0, hpos⟩ = (p : D) ∧
      (∀ i, z i ∈ maximalIdeal D) ∧ IsSystemOfParameters D z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  apply exists_isSystemOfParameters_head_eq D (p : D)
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  · rw [← residue_eq_zero_iff]
    simp only [map_natCast, CharP.cast_eq_zero]
  · simpa only [Nat.cast_succ] using hdim

end Parameters

section Construction

open IsLocalRing

/-- Witt係数と指定パラメータを評価し、有限な環写像を構成する。
係数写像の存在やパラメータ選択と区別した、実構成の接続定理。 -/
theorem exists_finite_wittPowerSeries_map_of_parameters
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    (φ : WittVector p (ResidueField D) →+* D)
    (hφ : (residue D).comp φ = WittVector.constantCoeff)
    {h : ℕ} (hpos : 0 < h) (z : Fin h → D) (hz0 : z ⟨0, hpos⟩ = (p : D))
    (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0}
        (WittVector p (ResidueField D)) →+* D,
      F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
        ∀ i, F (wittPowerSeriesParameter (ResidueField D) p i) = z i := by
  classical
  let W := WittVector p (ResidueField D)
  let σ := {i : Fin h // (i : ℕ) ≠ 0}
  let A := MvPowerSeries σ W
  let J := Ideal.span (Set.range z)
  have hJm : J ≤ maximalIdeal D := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzm i
  let : IsAdicComplete J D := isAdicComplete_finite_of_le_maximalIdeal J hJm
  let x : σ → D := fun i ↦ z i.val
  have hx (i : σ) : x i ∈ J := Ideal.subset_span (Set.mem_range_self i.val)
  let F : A →+* D := adicPowerSeriesEval φ J x hx
  have ht (i : Fin h) : F (wittPowerSeriesParameter (ResidueField D) p i) = z i := by
    by_cases hi : (i : ℕ) = 0
    · have he : i = ⟨0, hpos⟩ := Fin.ext hi
      subst i
      rw [wittPowerSeriesParameter_zero, map_natCast, hz0]
    · rw [wittPowerSeriesParameter_nonzero _ _ i hi]
      exact adicPowerSeriesEval_X φ J x hx ⟨i, hi⟩
  have hφres : Function.Surjective ((residue D).comp φ) := by
    rw [hφ]
    exact WittVector.constantCoeff_surjective p
  have hres : Function.Surjective ((residue D).comp F) := by
    intro a
    obtain ⟨w, hw⟩ := hφres a
    refine ⟨MvPowerSeries.C w, ?_⟩
    change residue D (adicPowerSeriesEval φ J x hx (MvPowerSeries.C w)) = a
    rw [adicPowerSeriesEval_C]
    exact hw
  let : Algebra W D := φ.toAlgebra
  let : Module.Finite W (D ⧸ J) := finite_quotient_of_common_residue_primary hφres J hprimary
  let : IsAdicComplete (maximalIdeal W) W := by
    rw [(WittVector.irreducible p).maximalIdeal_eq]
    infer_instance
  let : IsAdicComplete (maximalIdeal A) A := isAdicComplete_powerSeries_maximalIdeal σ W
  have hmap : (maximalIdeal A).map F = J := by
    rw [← span_wittPowerSeriesParameter_eq_maximalIdeal hpos (ResidueField D) p,
      Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext ht))
  have hfinite : F.Finite := adicPowerSeriesEval_finite J x hx (maximalIdeal A) hmap
  exact ⟨F, hfinite, hres, ht⟩

/-- 完全剰余体の完備Noether混標数局所整域に対するCohen正規化。
基底は引用3と同じ実際のWitt係数冪級数環であり、有限性と単射性を証明する。 -/
theorem exists_cohen_normalization_mixedCharacteristic
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [CharZero D] [IsAdicComplete (maximalIdeal D) D]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧
      ∃ (t : Fin h → A)
        (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D))),
        Ideal.span (Set.range t) = maximalIdeal A ∧ t ⟨0, hpos⟩ = (p : A) ∧
        ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩ := by
  obtain ⟨φ, hφ⟩ := exists_wittVector_residue_lift D p
  obtain ⟨z, hz0, hzm, hz⟩ := exists_mixedCharacteristic_systemOfParameters D p hdim hpos
  obtain ⟨F, hF, hres, _⟩ := exists_finite_wittPowerSeries_map_of_parameters D p φ hφ
    hpos z hz0 hzm hz.2
  let A := MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D))
  let : IsRegularLocalRing A := isRegularLocalRing_wittPowerSeries _ _ p
  let : IsAdicComplete (maximalIdeal A) A := by
    rw [wittPowerSeries_maximalIdeal_eq]
    exact isAdicComplete_wittPowerSeries_p_sup_variables _ _ p
  let : Algebra A D := F.toAlgebra
  have hinj : Function.Injective F := ringHom_injective_of_finite_of_equal_dimension F hF
    (ringKrullDim_wittNormalizationBase hpos (ResidueField D) p) hdim
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hinj, hF, hres, wittPowerSeriesParameter (ResidueField D) p, RingEquiv.refl A,
    span_wittPowerSeriesParameter_eq_maximalIdeal hpos _ p,
    wittPowerSeriesParameter_zero hpos _ p, ?_⟩
  intro i hi
  exact wittPowerSeriesParameter_nonzero _ _ i hi

end Construction

end SerrePositivity
