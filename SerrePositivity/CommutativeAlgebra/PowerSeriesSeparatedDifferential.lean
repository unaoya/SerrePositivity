module

public import SerrePositivity.CommutativeAlgebra.SeparatedPowerSeriesKaehler
public import SerrePositivity.CommutativeAlgebra.AdicModuleProducts

/-! # 通常の微分の変数進分離商

通常の Ω の分離商を有限自由加群へ実際に同定する。
通常の Ω 自身が有限自由であるとは主張しない。
-/

@[expose] public section
namespace SerrePositivity

variable {σ R : Type*} [Fintype σ] [CommRing R]
local notation "S" => MvPowerSeries σ R
local notation "J" => Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
local notation "Ω₀" => KaehlerDifferential R S

/-- 通常の微分から偏微分の組への写像。 -/
noncomputable def powerSeriesKaehlerToFree : Ω₀ →ₗ[S] (σ → S) :=
  (powerSeriesContinuousDifferential (σ := σ) (R := R)).liftKaehlerDifferential

open Classical in
@[simp] theorem powerSeriesKaehlerToFree_D_X (i : σ) :
    powerSeriesKaehlerToFree (KaehlerDifferential.D R S (MvPowerSeries.X i)) = Pi.single i 1 := by
  rw [powerSeriesKaehlerToFree, Derivation.liftKaehlerDifferential_comp_D,
    powerSeriesContinuousDifferential_X]

/-- 分離商から自由加群への写像と、標準基底をdX_iへ送る逆写像を構成する。 -/
theorem exists_powerSeriesHausdorffificationEquiv :
    ∃ E : Hausdorffification J Ω₀ ≃ₗ[S] (σ → S),
      ∀ ω, E (Hausdorffification.of J Ω₀ ω) = powerSeriesKaehlerToFree ω := by
  classical
  let H := Hausdorffification J Ω₀
  let : IsAdicComplete J (σ → S) := isAdicComplete_function J
  let L : H →ₗ[S] (σ → S) := Hausdorffification.lift J powerSeriesKaehlerToFree
  let V : (σ → S) →ₗ[S] H := Module.piEquiv σ S H
    (fun i ↦ Hausdorffification.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)))
  have hL (ω : Ω₀) : L (Hausdorffification.of J Ω₀ ω) = powerSeriesKaehlerToFree ω :=
    Hausdorffification.lift_of J powerSeriesKaehlerToFree ω
  have hV (i : σ) : V ((Pi.basisFun S σ) i) =
      Hausdorffification.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)) := by
    simp [V, Module.piEquiv]
  have hLV : L.comp V = LinearMap.id := by
    apply (Pi.basisFun S σ).ext
    intro i
    change L (V ((Pi.basisFun S σ) i)) = (Pi.basisFun S σ) i
    rw [hV, hL, powerSeriesKaehlerToFree_D_X, Pi.basisFun_apply]
  have hVL : V.comp L = LinearMap.id := by
    have he : (V.comp L).comp (Hausdorffification.of J Ω₀) = Hausdorffification.of J Ω₀ := by
      let : IsScalarTower R S H := inferInstance
      apply powerSeries_kaehler_linearMap_ext_of_isHausdorff
      intro i
      change V (L (Hausdorffification.of J Ω₀
        (KaehlerDifferential.D R S (MvPowerSeries.X i)))) = _
      rw [hL, powerSeriesKaehlerToFree_D_X, ← Pi.basisFun_apply, hV]
    apply LinearMap.ext
    intro x
    induction x using Hausdorffification.induction_on with
    | ih ω => exact LinearMap.congr_fun he ω
  refine ⟨LinearEquiv.ofLinearMap L V hLV hVL, ?_⟩
  intro ω
  exact Hausdorffification.lift_of J powerSeriesKaehlerToFree ω

/-- 通常のΩの変数進分離商と有限自由加群の実際の線形同型。 -/
noncomputable def powerSeriesHausdorffificationEquiv :
    Hausdorffification J Ω₀ ≃ₗ[S] (σ → S) :=
  exists_powerSeriesHausdorffificationEquiv.choose

@[simp] theorem powerSeriesHausdorffificationEquiv_of (ω : Ω₀) :
    powerSeriesHausdorffificationEquiv (Hausdorffification.of J Ω₀ ω) =
      powerSeriesKaehlerToFree ω :=
  exists_powerSeriesHausdorffificationEquiv.choose_spec ω

end SerrePositivity
