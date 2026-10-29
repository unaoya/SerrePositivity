module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.FiniteNormalizationTools
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import Mathlib.RingTheory.KrullDimension.Field

/-! # 有限な閉ファイバーからの冪級数の有限正規化

係数の剰余体への全射性は要求しない。評価先の指定イデアルの完備性と
その商の係数環上の有限性を供給すれば、同じ評価の有限性を得る。
-/

@[expose] public section
namespace SerrePositivity

/-- 各生成元を正の冪に変えても、生成イデアルの根基は変わらない。 -/
theorem radical_span_powers {R σ : Type*} [CommRing R] (z : σ → R) (n : σ → ℕ)
    (hn : ∀ i, 0 < n i) :
    (Ideal.span (Set.range (fun i ↦ z i ^ n i))).radical = (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Ideal.span (Set.range z)).pow_mem_of_mem
      (Ideal.subset_span (Set.mem_range_self i)) _ (hn i)
  · have hle : Ideal.span (Set.range z) ≤
        (Ideal.span (Set.range (fun i ↦ z i ^ n i))).radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨n i, Ideal.subset_span (Set.mem_range_self i)⟩
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hle

/-- 有限閉ファイバーを持つ完備な評価先への、同じ係数・変数を保つ有限評価。 -/
theorem exists_finite_powerSeries_map_of_finite_quotient
    {k D σ : Type*} [CommRing k] [CommRing D] [Algebra k D] [Finite σ]
    (z : σ → D) [IsAdicComplete (Ideal.span (Set.range z)) D]
    [Module.Finite k (D ⧸ Ideal.span (Set.range z))] :
    ∃ F : MvPowerSeries σ k →+* D,
      F.Finite ∧ (∀ a, F (MvPowerSeries.C a) = algebraMap k D a) ∧
        ∀ i, F (MvPowerSeries.X i) = z i := by
  let J := Ideal.span (Set.range z)
  have hz (i : σ) : z i ∈ J := Ideal.subset_span (Set.mem_range_self i)
  let F := adicPowerSeriesEval (algebraMap k D) J z hz
  exact ⟨F, adicPowerSeriesEval_finite_of_span J z hz rfl,
    adicPowerSeriesEval_C _ J z hz, adicPowerSeriesEval_X _ J z hz⟩

/-- 次元が変数の個数と一致すれば、上の同じ有限評価は単射。
評価先のNoether性・局所性・整域性は要求しない。 -/
theorem exists_injective_finite_powerSeries_map_of_finite_quotient
    {k D : Type*} [Field k] [CommRing D] [Algebra k D]
    {h : ℕ} (hdim : ringKrullDim D = h) (z : Fin h → D)
    [IsAdicComplete (Ideal.span (Set.range z)) D]
    [Module.Finite k (D ⧸ Ideal.span (Set.range z))] :
    ∃ F : MvPowerSeries (Fin h) k →+* D,
      Function.Injective F ∧ F.Finite ∧ (∀ a, F (MvPowerSeries.C a) = algebraMap k D a) ∧
        ∀ i, F (MvPowerSeries.X i) = z i := by
  obtain ⟨F, hf, hC, hX⟩ := exists_finite_powerSeries_map_of_finite_quotient (k := k) z
  have hA : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
    rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_eq_zero_of_field, zero_add]
  exact ⟨F, ringHom_injective_of_finite_of_equal_dimension F hf hA hdim, hf, hC, hX⟩

/-- 変数の像を指定した環写像は、変数イデアルを指定族の生成イデアルへ送る。 -/
theorem map_powerSeries_variables_eq_span
    {k D σ : Type*} [CommRing k] [CommRing D]
    (F : MvPowerSeries σ k →+* D) (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i) :
    (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map F =
      Ideal.span (Set.range z) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext hX)

end SerrePositivity
