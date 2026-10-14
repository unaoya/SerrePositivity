module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesSeparatedDifferential
public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # 通常の微分の変数進完備化

通常の Ω の完備化と有限自由加群の写像を構成し、元の微分との両立を確認する。
-/

@[expose] public section
namespace SerrePositivity

variable {σ R : Type*} [Fintype σ] [CommRing R]
local notation "S" => MvPowerSeries σ R
local notation "J" => Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
local notation "Ω₀" => KaehlerDifferential R S

/-- 完備化へ偏微分の写像を延長し、基底上の逆写像と比較する。 -/
theorem exists_powerSeriesCompletedDifferentialEquiv :
    ∃ E : AdicCompletion J Ω₀ ≃ₗ[S] (σ → S),
      ∀ ω, E (AdicCompletion.of J Ω₀ ω) = powerSeriesKaehlerToFree ω := by
  classical
  have hJ : (J).FG := Submodule.fg_span (Set.finite_range _)
  let C := AdicCompletion J Ω₀
  let : IsAdicComplete J C := AdicCompletion.isAdicComplete hJ
  let : IsAdicComplete J (σ → S) := isAdicComplete_function J
  let L : C →ₗ[S] (σ → S) := (AdicCompletion.ofLinearEquiv J (σ → S)).symm.toLinearMap.comp
    ((AdicCompletion.map J powerSeriesKaehlerToFree).restrictScalars S)
  let V : (σ → S) →ₗ[S] C := Module.piEquiv σ S C
    (fun i ↦ AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)))
  have hL (ω : Ω₀) : L (AdicCompletion.of J Ω₀ ω) = powerSeriesKaehlerToFree ω := by
    change (AdicCompletion.ofLinearEquiv J (σ → S)).symm
      (AdicCompletion.map J powerSeriesKaehlerToFree (AdicCompletion.of J Ω₀ ω)) = _
    rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  have hV (i : σ) : V ((Pi.basisFun S σ) i) =
      AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)) := by
    simp [V, Module.piEquiv]
  have hLV : L.comp V = LinearMap.id := by
    apply (Pi.basisFun S σ).ext
    intro i
    change L (V ((Pi.basisFun S σ) i)) = (Pi.basisFun S σ) i
    rw [hV, hL, powerSeriesKaehlerToFree_D_X, Pi.basisFun_apply]
  have hVL : V.comp L = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of J hJ
    let : IsScalarTower R S C := inferInstance
    apply powerSeries_kaehler_linearMap_ext_of_isHausdorff
    intro i
    change V (L (AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)))) = _
    rw [hL, powerSeriesKaehlerToFree_D_X, ← Pi.basisFun_apply, hV]
    rfl
  refine ⟨LinearEquiv.ofLinearMap L V hLV hVL, hL⟩

/-- 通常Ωの変数イデアル進完備化と有限自由加群の実際の線形同型。 -/
noncomputable def powerSeriesCompletedDifferentialEquiv : AdicCompletion J Ω₀ ≃ₗ[S] (σ → S) :=
  exists_powerSeriesCompletedDifferentialEquiv.choose

@[simp] theorem powerSeriesCompletedDifferentialEquiv_of (ω : Ω₀) :
    powerSeriesCompletedDifferentialEquiv (AdicCompletion.of J Ω₀ ω) = powerSeriesKaehlerToFree ω :=
  exists_powerSeriesCompletedDifferentialEquiv.choose_spec ω

open Classical in
/-- 完備化した変数の微分は、同型で対応する標準基底に移る。 -/
@[simp] theorem powerSeriesCompletedDifferentialEquiv_D_X (i : σ) :
    powerSeriesCompletedDifferentialEquiv
      (AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i))) = Pi.single i 1 := by
  rw [powerSeriesCompletedDifferentialEquiv_of, powerSeriesKaehlerToFree_D_X]

/-- 完備化した変数の微分を基底とする、実際の有限自由基底。 -/
noncomputable def powerSeriesCompletedDifferentialBasis :
    Module.Basis σ S (AdicCompletion J Ω₀) :=
  (Pi.basisFun S σ).map powerSeriesCompletedDifferentialEquiv.symm

@[simp] theorem powerSeriesCompletedDifferentialBasis_apply (i : σ) :
    powerSeriesCompletedDifferentialBasis i =
      AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)) := by
  classical
  rw [powerSeriesCompletedDifferentialBasis, Module.Basis.map_apply]
  apply powerSeriesCompletedDifferentialEquiv.injective
  rw [LinearEquiv.apply_symm_apply, powerSeriesCompletedDifferentialEquiv_D_X,
    Pi.basisFun_apply]

omit [Fintype σ] in
theorem moduleFree_powerSeriesCompletedDifferential [Finite σ] :
    Module.Free S (AdicCompletion J Ω₀) := by
  let := Fintype.ofFinite σ
  exact Module.Free.of_basis powerSeriesCompletedDifferentialBasis

omit [Fintype σ] in
theorem moduleFinite_powerSeriesCompletedDifferential [Finite σ] :
    Module.Finite S (AdicCompletion J Ω₀) := by
  let := Fintype.ofFinite σ
  exact Module.Finite.of_basis powerSeriesCompletedDifferentialBasis

end SerrePositivity
