module

public import SerrePositivity.CommutativeAlgebra.ContinuousPowerSeriesDerivation
public import Mathlib.LinearAlgebra.StdBasis

/-! # 連続導分を表現する有限自由加群

積位相に関して、有限自由加群と偏微分の組が連続導分を表現する。
通常の Kähler 微分の完備化との同定はここでは主張しない。
-/

@[expose] public section
namespace SerrePositivity
open scoped MvPowerSeries.WithPiTopology

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- 偏微分を並べた、有限自由加群への導分。 -/
noncomputable def powerSeriesContinuousDifferential :
    Derivation R (MvPowerSeries σ R) (σ → MvPowerSeries σ R) := by
  classical
  exact powerSeriesDerivation (R := R) (fun i ↦ Pi.single i 1)

@[simp] theorem powerSeriesContinuousDifferential_apply (f : MvPowerSeries σ R) (i : σ) :
    powerSeriesContinuousDifferential f i = MvPowerSeries.pderiv (R := R) i f := by
  classical
  simp [powerSeriesContinuousDifferential, powerSeriesDerivation_apply, Pi.single_apply]

open Classical in
/-- 形式変数の微分は対応する標準基底ベクトル。 -/
@[simp] theorem powerSeriesContinuousDifferential_X (j : σ) :
    powerSeriesContinuousDifferential (MvPowerSeries.X (R := R) j) = Pi.single j 1 := by
  classical
  funext i
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, eq_comm]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_powerSeriesContinuousDifferential :
    Continuous (powerSeriesContinuousDifferential (σ := σ) (R := R)) := by
  apply continuous_pi
  intro i
  simpa only [powerSeriesContinuousDifferential_apply] using
    continuous_powerSeries_pderiv (R := R) i

variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
  [IsScalarTower R (MvPowerSeries σ R) M] [TopologicalSpace M] [T2Space M]
  [IsTopologicalAddGroup M] [ContinuousSMul (MvPowerSeries σ R) M]

/-- 連続導分と有限自由加群からの線形写像との実際の線形同型。 -/
noncomputable def powerSeriesContinuousDifferentialLiftEquiv :
    continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M) ≃ₗ[MvPowerSeries σ R]
      ((σ → MvPowerSeries σ R) →ₗ[MvPowerSeries σ R] M) :=
  continuousPowerSeriesDerivationEquiv.trans (Module.piEquiv σ (MvPowerSeries σ R) M)

/-- 対応する線形写像は、自由加群への導分を元の連続導分へ送る。 -/
theorem powerSeriesContinuousDifferentialLiftEquiv_comp
    (δ : continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M)) (f : MvPowerSeries σ R) :
    powerSeriesContinuousDifferentialLiftEquiv δ (powerSeriesContinuousDifferential f) =
      δ.val f := by
  change Module.piEquiv σ (MvPowerSeries σ R) M (fun i ↦ δ.val (MvPowerSeries.X i))
    (powerSeriesContinuousDifferential f) = _
  rw [Module.piEquiv_apply_apply]
  simp only [powerSeriesContinuousDifferential_apply]
  rw [← powerSeriesDerivation_apply]
  have he : powerSeriesDerivation (R := R) (fun i ↦ δ.val (MvPowerSeries.X i)) = δ.val :=
    continuous_powerSeries_derivation_ext _ _ (continuous_powerSeriesDerivation _) δ.property
      (fun i ↦ powerSeriesDerivation_X _ i)
  exact congrArg (fun d : Derivation R (MvPowerSeries σ R) M ↦ d f) he

/-- 表現する線形写像自身も連続である。有限自由性と連続な係数作用を使う。 -/
theorem continuous_powerSeriesContinuousDifferentialLiftEquiv
    (δ : continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M)) :
    Continuous (powerSeriesContinuousDifferentialLiftEquiv δ) := by
  change Continuous (Module.piEquiv σ (MvPowerSeries σ R) M
    (fun i ↦ δ.val (MvPowerSeries.X i)))
  have he : (Module.piEquiv σ (MvPowerSeries σ R) M
      (fun i ↦ δ.val (MvPowerSeries.X i)) : (σ → MvPowerSeries σ R) → M) =
      (fun v ↦ ∑ i, v i • δ.val (MvPowerSeries.X i)) :=
    funext (Module.piEquiv_apply_apply _ _ _ _)
  rw [he]
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_apply i).smul continuous_const)

end SerrePositivity
