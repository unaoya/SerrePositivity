module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesCompletedDifferential
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # 冪級数微分の係数拡大と完備化

A=k[[X]]の通常微分の係数拡大S⊗_A Ω_{A/k}を、変数イデアルの像Iに沿って完備化する。
SがI進完備なら、この完備化は変数の微分を基底とするSの有限自由加群。
通常Ωの有限生成性・係数拡大の有限性や平坦性・Noether性は仮定しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open TensorProduct

variable {σ k S : Type*} [Fintype σ] [CommRing k] [CommRing S]
  [Algebra (MvPowerSeries σ k) S] [Algebra k S] [IsScalarTower k (MvPowerSeries σ k) S]
local notation "A" => MvPowerSeries σ k
local notation "J" => Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))
local notation "Iₛ" => Ideal.map (algebraMap A S) J
local notation "Ω₀" => KaehlerDifferential k A
local notation "T" => TensorProduct A S Ω₀

/-- 係数拡大した通常微分から偏微分の組への写像。 -/
def powerSeriesBaseChangeKaehlerToFree : T →ₗ[S] (σ → S) := by
  classical
  exact (TensorProduct.piScalarRight A S S σ).toLinearMap.comp
    (AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) powerSeriesKaehlerToFree)

omit [Algebra k S] [IsScalarTower k A S] in
open Classical in
@[simp] theorem powerSeriesBaseChangeKaehlerToFree_D_X (i : σ) :
    powerSeriesBaseChangeKaehlerToFree (S := S)
      (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)) = Pi.single i 1 := by
  ext j
  simp [powerSeriesBaseChangeKaehlerToFree, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Pi.single_apply]

omit [Fintype σ] [Algebra k S] [IsScalarTower k A S] in
/-- 分離した終域への係数拡大微分の写像は、変数の微分の像で決まる。 -/
theorem powerSeries_baseChange_kaehler_linearMap_ext_of_isHausdorff
    [Finite σ]
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [Module S M]
    [IsScalarTower k A M] [IsScalarTower A S M] [IsHausdorff Iₛ M]
    (f g : T →ₗ[S] M)
    (hX : ∀ i, f (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)) =
      g (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i))) : f = g := by
  let : IsHausdorff J M :=
    (IsHausdorff.map_algebraMap_iff (I := J) (S := S) (M := M)).mp inferInstance
  have he : (f.restrictScalars A).comp (TensorProduct.mk A S Ω₀ 1) =
      (g.restrictScalars A).comp (TensorProduct.mk A S Ω₀ 1) := by
    apply powerSeries_kaehler_linearMap_ext_of_isHausdorff
    exact hX
  apply AlgebraTensorModule.ext
  intro s ω
  have ht : s ⊗ₜ[A] ω = s • (1 ⊗ₜ[A] ω) := by
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  rw [ht, map_smul, map_smul]
  exact congrArg (s • ·) (LinearMap.congr_fun he ω)

variable [IsAdicComplete
  ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
    (algebraMap (MvPowerSeries σ k) S)) S]

/-- 係数拡大した通常微分の完備化を、標準基底と実際に同定する。 -/
theorem exists_powerSeriesBaseChangeCompletedDifferentialEquiv :
    ∃ E : AdicCompletion Iₛ T ≃ₗ[S] (σ → S),
      ∀ ω, E (AdicCompletion.of Iₛ T ω) = powerSeriesBaseChangeKaehlerToFree ω := by
  classical
  have hJ : (J).FG := Submodule.fg_span (Set.finite_range _)
  have hI : (Iₛ).FG := Ideal.FG.map hJ (algebraMap A S)
  let C := AdicCompletion Iₛ T
  let : IsAdicComplete Iₛ C := AdicCompletion.isAdicComplete hI
  let : IsAdicComplete Iₛ (σ → S) := isAdicComplete_function Iₛ
  let L : C →ₗ[S] (σ → S) := (AdicCompletion.ofLinearEquiv Iₛ (σ → S)).symm.toLinearMap.comp
    ((AdicCompletion.map Iₛ powerSeriesBaseChangeKaehlerToFree).restrictScalars S)
  let V : (σ → S) →ₗ[S] C := Module.piEquiv σ S C (fun i ↦
    AdicCompletion.of Iₛ T (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)))
  have hL (ω : T) : L (AdicCompletion.of Iₛ T ω) = powerSeriesBaseChangeKaehlerToFree ω := by
    change (AdicCompletion.ofLinearEquiv Iₛ (σ → S)).symm
      (AdicCompletion.map Iₛ powerSeriesBaseChangeKaehlerToFree (AdicCompletion.of Iₛ T ω)) = _
    rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  have hV (i : σ) : V ((Pi.basisFun S σ) i) =
      AdicCompletion.of Iₛ T (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)) := by
    simp [V, Module.piEquiv]
  have hLV : L.comp V = LinearMap.id := by
    apply (Pi.basisFun S σ).ext
    intro i
    change L (V ((Pi.basisFun S σ) i)) = (Pi.basisFun S σ) i
    rw [hV, hL, powerSeriesBaseChangeKaehlerToFree_D_X, Pi.basisFun_apply]
  have hVL : V.comp L = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of Iₛ hI
    let : IsScalarTower k A C := inferInstance
    let : IsScalarTower A S C := inferInstance
    apply powerSeries_baseChange_kaehler_linearMap_ext_of_isHausdorff
    intro i
    change V (L (AdicCompletion.of Iₛ T
      (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)))) = _
    rw [hL, powerSeriesBaseChangeKaehlerToFree_D_X, ← Pi.basisFun_apply, hV]
    rfl
  exact ⟨LinearEquiv.ofLinearMap L V hLV hVL, hL⟩

def powerSeriesBaseChangeCompletedDifferentialEquiv : AdicCompletion Iₛ T ≃ₗ[S] (σ → S) :=
  exists_powerSeriesBaseChangeCompletedDifferentialEquiv.choose

@[simp] theorem powerSeriesBaseChangeCompletedDifferentialEquiv_of (ω : T) :
    powerSeriesBaseChangeCompletedDifferentialEquiv (AdicCompletion.of Iₛ T ω) =
      powerSeriesBaseChangeKaehlerToFree ω :=
  exists_powerSeriesBaseChangeCompletedDifferentialEquiv.choose_spec ω

/-- 完備してから係数拡大する加群と、係数拡大してから完備する加群の同型。 -/
def powerSeriesCompletedDifferentialTensorEquiv :
    TensorProduct A S (AdicCompletion J Ω₀) ≃ₗ[S] AdicCompletion Iₛ T := by
  classical
  exact ((AlgebraTensorModule.congr (LinearEquiv.refl S S)
    powerSeriesCompletedDifferentialEquiv).trans (TensorProduct.piScalarRight A S S σ)).trans
      powerSeriesBaseChangeCompletedDifferentialEquiv.symm

/-- 比較同型は元の微分のテンソルに対し標準写像と両立する。 -/
@[simp] theorem powerSeriesCompletedDifferentialTensorEquiv_tmul_of (s : S) (ω : Ω₀) :
    powerSeriesCompletedDifferentialTensorEquiv (s ⊗ₜ[A] AdicCompletion.of J Ω₀ ω) =
      AdicCompletion.of Iₛ T (s ⊗ₜ[A] ω) := by
  classical
  apply powerSeriesBaseChangeCompletedDifferentialEquiv.injective
  simp [powerSeriesCompletedDifferentialTensorEquiv, LinearEquiv.trans_apply,
    powerSeriesBaseChangeKaehlerToFree]

/-- 係数拡大した変数の微分の完備化を基底とする。 -/
def powerSeriesBaseChangeCompletedDifferentialBasis :
    Module.Basis σ S (AdicCompletion Iₛ T) :=
  (Pi.basisFun S σ).map powerSeriesBaseChangeCompletedDifferentialEquiv.symm

@[simp] theorem powerSeriesBaseChangeCompletedDifferentialBasis_apply (i : σ) :
    powerSeriesBaseChangeCompletedDifferentialBasis (S := S) i =
      AdicCompletion.of Iₛ T (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)) := by
  classical
  rw [powerSeriesBaseChangeCompletedDifferentialBasis, Module.Basis.map_apply]
  apply powerSeriesBaseChangeCompletedDifferentialEquiv.injective
  rw [LinearEquiv.apply_symm_apply, powerSeriesBaseChangeCompletedDifferentialEquiv_of,
    powerSeriesBaseChangeKaehlerToFree_D_X, Pi.basisFun_apply]

omit [Fintype σ] in
theorem moduleFree_powerSeriesBaseChangeCompletedDifferential [Finite σ] :
    Module.Free S (AdicCompletion Iₛ T) := by
  let := Fintype.ofFinite σ
  exact Module.Free.of_basis powerSeriesBaseChangeCompletedDifferentialBasis

omit [Fintype σ] in
theorem moduleFinite_powerSeriesBaseChangeCompletedDifferential [Finite σ] :
    Module.Finite S (AdicCompletion Iₛ T) := by
  let := Fintype.ofFinite σ
  exact Module.Finite.of_basis powerSeriesBaseChangeCompletedDifferentialBasis

end SerrePositivity
