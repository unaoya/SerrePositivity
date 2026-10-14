module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesBaseChangeDifferential
public import SerrePositivity.CommutativeAlgebra.PrimaryCompletedDifferential

/-! # 完備した冪級数微分からの推移列

係数拡大と完備化の比較を最初の写像へ組み込み、有限型の閉ファイバーから
中項の有限性を供給する。通常の絶対微分の有限性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open TensorProduct

variable {σ k S : Type*} [Fintype σ] [CommRing k] [CommRing S]
  [Algebra (MvPowerSeries σ k) S] [Algebra k S] [IsScalarTower k (MvPowerSeries σ k) S]
  [IsAdicComplete
    ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S)) S]
local notation "A" => MvPowerSeries σ k
local notation "J" => Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))
local notation "Iₛ" => Ideal.map (algebraMap A S) J
local notation "Ω₀" => KaehlerDifferential k A

/-- 完備した基底微分の係数拡大から、完備絶対微分への実際の写像。 -/
def powerSeriesCompletedDifferentialMap :
    TensorProduct A S (AdicCompletion J Ω₀) →ₗ[S]
      AdicCompletion Iₛ (KaehlerDifferential k S) :=
  (completedDifferentialBaseChange (R := A) Iₛ k).comp
    powerSeriesCompletedDifferentialTensorEquiv.toLinearMap

@[simp] theorem powerSeriesCompletedDifferentialMap_tmul_of (s : S) (ω : Ω₀) :
    powerSeriesCompletedDifferentialMap (s ⊗ₜ[A] AdicCompletion.of J Ω₀ ω) =
      AdicCompletion.of Iₛ (KaehlerDifferential k S)
        (s • KaehlerDifferential.map k k A S ω) := by
  simp [powerSeriesCompletedDifferentialMap, KaehlerDifferential.mapBaseChange_tmul]

/-- 最初の写像の像は、変数の像の微分が生成する部分加群。 -/
theorem range_powerSeriesCompletedDifferentialMap_eq_span :
    LinearMap.range (powerSeriesCompletedDifferentialMap (σ := σ) (k := k) (S := S)) =
      Submodule.span S (Set.range fun i : σ ↦
        AdicCompletion.of Iₛ (KaehlerDifferential k S)
          (KaehlerDifferential.D k S (algebraMap A S (MvPowerSeries.X i)))) := by
  rw [powerSeriesCompletedDifferentialMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  let f := completedDifferentialBaseChange (R := A) Iₛ k
  let B := powerSeriesBaseChangeCompletedDifferentialBasis (σ := σ) (k := k) (S := S)
  have hf : f = B.constr ℕ (fun i ↦ f (B i)) := (B.constr_self ℕ f).symm
  change LinearMap.range f = _
  rw [hf, Module.Basis.constr_range]
  congr 1
  funext i
  simp [f, B, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

variable [Algebra.EssFiniteType (MvPowerSeries σ k) S] [IsNoetherianRing S] [IsLocalRing S]
  [Algebra.EssFiniteType k
    (S ⧸ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S))]

/-- 比較同型により、完備した基底微分からの像が係数制限の核に一致する。 -/
theorem range_powerSeriesCompletedDifferentialMap_eq_ker (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    LinearMap.range (powerSeriesCompletedDifferentialMap (σ := σ) (k := k) (S := S)) =
      LinearMap.ker (completedDifferentialRestriction (R := A) Iₛ hI k) := by
  rw [powerSeriesCompletedDifferentialMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact range_completedDifferentialBaseChange_eq_ker_of_finiteType_fiber (k := k) Iₛ hI

/-- 完備微分の推移列は、完備した基底微分のテンソル積を最初の項として完全。 -/
theorem exact_powerSeriesCompletedDifferentialMap_restriction
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    Function.Exact (powerSeriesCompletedDifferentialMap (σ := σ) (k := k) (S := S))
      (completedDifferentialRestriction (R := A) Iₛ hI k) :=
  SetLike.ext_iff.mp (range_powerSeriesCompletedDifferentialMap_eq_ker hI).symm

omit [Fintype σ] in
/-- 係数制限の核を、パラメータの微分の生成する部分加群として計算する。 -/
theorem ker_powerSeriesCompletedDifferentialRestriction_eq_span
    [Finite σ]
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    LinearMap.ker (completedDifferentialRestriction (R := A) Iₛ hI k) =
      Submodule.span S (Set.range fun i : σ ↦
        AdicCompletion.of Iₛ (KaehlerDifferential k S)
          (KaehlerDifferential.D k S (algebraMap A S (MvPowerSeries.X i)))) := by
  let := Fintype.ofFinite σ
  rw [← range_powerSeriesCompletedDifferentialMap_eq_ker hI,
    range_powerSeriesCompletedDifferentialMap_eq_span]

end SerrePositivity
