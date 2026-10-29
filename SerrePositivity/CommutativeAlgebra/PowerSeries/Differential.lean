module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Derivation
public import SerrePositivity.CommutativeAlgebra.CompletedDifferential
public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import SerrePositivity.CommutativeAlgebra.AdicModuleProducts
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # 冪級数環の完備 Kähler 微分

概要：有限変数の冪級数環 `A = k[[X]]` について
- `Ω̂_{A/k} = (Ω_{A/k})^∧_{(X)}` は `dX_i` を基底とする有限自由 `A` 加群。
- `A → S` で `S` が `I = (X)S` 進完備なら、`(S ⊗_A Ω_{A/k})^∧_I` は `1 ⊗ dX_i` を基底とする有限自由 `S` 加群。
- さらに `S` が Noether 局所で `S/A` と閉ファイバーが本質的に有限型なら、係数制限
  `Ω̂_{S/k} → Ω_{S/A}` の核は変数の像の微分で張られる。変数が `p` 乗元へ送られるなら核は零で、
  `Ω̂_{S/k} ≅ Ω_{S/A}`。
方針：自由性は、偏微分を並べた写像 `Ω_{A/k} → A^σ` を完備化したものと、`dX_i` への逆写像が互いに逆であることから。
逆向きの合成が恒等であることは、分離な加群への写像が `dX_i` の像で決まること
（`powerSeries_kaehler_linearMap_ext_of_isHausdorff`）による。核は完備微分の推移列（`CompletedDifferential`）で計算する。
規約：`Ω_{A/k}` 自身の有限生成性は仮定しない。
使われ方：中間係数体上の完備微分の比較（`CofiniteCompletedDifferentialComparison`）と Cohen–Gabber。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open TensorProduct

section Helper

variable {S C σ : Type*} [CommRing S] [AddCommGroup C] [Module S C] [Fintype σ] [DecidableEq σ]

/-- 自由加群への写像 `L` が族 `g` を標準基底へ送り、`C` の自己準同型が `g` の上で決まるなら、`L` は同型。 -/
def linearEquivPiOfGenerators (L : C →ₗ[S] (σ → S)) (g : σ → C)
    (hLg : ∀ i, L (g i) = Pi.single i 1)
    (hext : ∀ u v : C →ₗ[S] C, (∀ i, u (g i) = v (g i)) → u = v) : C ≃ₗ[S] (σ → S) :=
  LinearEquiv.ofLinearMap L (Module.piEquiv σ S C g)
    ((Pi.basisFun S σ).ext fun i ↦ by
      simp [Module.piEquiv_apply_apply, Pi.single_apply, hLg])
    (hext _ _ fun i ↦ by simp [Module.piEquiv_apply_apply, hLg, Pi.single_apply])

@[simp] theorem linearEquivPiOfGenerators_apply (L : C →ₗ[S] (σ → S)) (g : σ → C) (hLg hext)
    (x : C) : linearEquivPiOfGenerators L g hLg hext x = L x := rfl

theorem linearEquivPiOfGenerators_symm_single (L : C →ₗ[S] (σ → S)) (g : σ → C) (hLg hext)
    (i : σ) : (linearEquivPiOfGenerators L g hLg hext).symm (Pi.single i 1) = g i := by
  apply (linearEquivPiOfGenerators L g hLg hext).injective
  rw [LinearEquiv.apply_symm_apply, linearEquivPiOfGenerators_apply, hLg]

end Helper

section Absolute

variable {σ R : Type*} [Fintype σ] [CommRing R]
local notation "S" => MvPowerSeries σ R
local notation "J" => Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
local notation "Ω₀" => KaehlerDifferential R S

/-- 通常の微分から偏微分の組への写像。 -/
def powerSeriesKaehlerToFree : Ω₀ →ₗ[S] (σ → S) :=
  (powerSeriesContinuousDifferential (σ := σ) (R := R)).liftKaehlerDifferential

open Classical in
@[simp] theorem powerSeriesKaehlerToFree_D_X (i : σ) :
    powerSeriesKaehlerToFree (KaehlerDifferential.D R S (MvPowerSeries.X i)) = Pi.single i 1 := by
  rw [powerSeriesKaehlerToFree, Derivation.liftKaehlerDifferential_comp_D,
    powerSeriesContinuousDifferential_X]

open Classical in
/-- `Ω̂_{A/k} ≅ A^σ`。完備化した `dX_i` が標準基底に対応する。 -/
def powerSeriesCompletedDifferentialEquiv : AdicCompletion J Ω₀ ≃ₗ[S] (σ → S) :=
  letI : IsAdicComplete J (σ → S) := isAdicComplete_function J
  linearEquivPiOfGenerators
    ((AdicCompletion.ofLinearEquiv J (σ → S)).symm.toLinearMap.comp
      ((AdicCompletion.map J powerSeriesKaehlerToFree).restrictScalars S))
    (fun i ↦ AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)))
    (fun i ↦ by
      simp [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of])
    (fun u v h ↦ by
      have hJ : (J).FG := Submodule.fg_span (Set.finite_range _)
      let : IsAdicComplete J (AdicCompletion J Ω₀) := AdicCompletion.isAdicComplete hJ
      apply adicCompletion_linearMap_ext_of_of J hJ
      exact powerSeries_kaehler_linearMap_ext_of_isHausdorff _ _ h)

@[simp] theorem powerSeriesCompletedDifferentialEquiv_of (ω : Ω₀) :
    powerSeriesCompletedDifferentialEquiv (AdicCompletion.of J Ω₀ ω) =
      powerSeriesKaehlerToFree ω := by
  let : IsAdicComplete J (σ → S) := isAdicComplete_function J
  simp [powerSeriesCompletedDifferentialEquiv, AdicCompletion.map_of,
    AdicCompletion.ofLinearEquiv_symm_of]

/-- 完備化した変数の微分を基底とする、`Ω̂_{A/k}` の有限自由基底。 -/
def powerSeriesCompletedDifferentialBasis : Module.Basis σ S (AdicCompletion J Ω₀) :=
  (Pi.basisFun S σ).map powerSeriesCompletedDifferentialEquiv.symm

@[simp] theorem powerSeriesCompletedDifferentialBasis_apply (i : σ) :
    powerSeriesCompletedDifferentialBasis i =
      AdicCompletion.of J Ω₀ (KaehlerDifferential.D R S (MvPowerSeries.X i)) := by
  classical
  rw [powerSeriesCompletedDifferentialBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  exact linearEquivPiOfGenerators_symm_single _ _ _ _ i

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

end Absolute

section BaseChange

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

open Classical in
/-- `(S ⊗_A Ω_{A/k})^∧_I ≅ S^σ`。`1 ⊗ dX_i` の完備化が標準基底に対応する。 -/
def powerSeriesBaseChangeCompletedDifferentialEquiv : AdicCompletion Iₛ T ≃ₗ[S] (σ → S) :=
  letI : IsAdicComplete Iₛ (σ → S) := isAdicComplete_function Iₛ
  linearEquivPiOfGenerators
    ((AdicCompletion.ofLinearEquiv Iₛ (σ → S)).symm.toLinearMap.comp
      ((AdicCompletion.map Iₛ powerSeriesBaseChangeKaehlerToFree).restrictScalars S))
    (fun i ↦ AdicCompletion.of Iₛ T (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)))
    (fun i ↦ by
      simp [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of])
    (fun u v h ↦ by
      have hJ : (J).FG := Submodule.fg_span (Set.finite_range _)
      have hI : (Iₛ).FG := Ideal.FG.map hJ (algebraMap A S)
      let : IsAdicComplete Iₛ (AdicCompletion Iₛ T) := AdicCompletion.isAdicComplete hI
      apply adicCompletion_linearMap_ext_of_of Iₛ hI
      exact powerSeries_baseChange_kaehler_linearMap_ext_of_isHausdorff _ _ h)

@[simp] theorem powerSeriesBaseChangeCompletedDifferentialEquiv_of (ω : T) :
    powerSeriesBaseChangeCompletedDifferentialEquiv (AdicCompletion.of Iₛ T ω) =
      powerSeriesBaseChangeKaehlerToFree ω := by
  let : IsAdicComplete Iₛ (σ → S) := isAdicComplete_function Iₛ
  simp [powerSeriesBaseChangeCompletedDifferentialEquiv, AdicCompletion.map_of,
    AdicCompletion.ofLinearEquiv_symm_of]

/-- 係数拡大した変数の微分の完備化を基底とする。 -/
def powerSeriesBaseChangeCompletedDifferentialBasis :
    Module.Basis σ S (AdicCompletion Iₛ T) :=
  (Pi.basisFun S σ).map powerSeriesBaseChangeCompletedDifferentialEquiv.symm

@[simp] theorem powerSeriesBaseChangeCompletedDifferentialBasis_apply (i : σ) :
    powerSeriesBaseChangeCompletedDifferentialBasis (S := S) i =
      AdicCompletion.of Iₛ T (1 ⊗ₜ[A] KaehlerDifferential.D k A (MvPowerSeries.X i)) := by
  classical
  rw [powerSeriesBaseChangeCompletedDifferentialBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  exact linearEquivPiOfGenerators_symm_single _ _ _ _ i

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

variable [Algebra.EssFiniteType (MvPowerSeries σ k) S] [IsNoetherianRing S] [IsLocalRing S]
  [Algebra.EssFiniteType k
    (S ⧸ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S))]

omit [Fintype σ] in
/-- 係数制限 `Ω̂_{S/k} → Ω_{S/A}` の核は、変数の像の微分が張る部分加群。 -/
theorem ker_powerSeriesCompletedDifferentialRestriction_eq_span [Finite σ]
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    LinearMap.ker (completedDifferentialRestriction (R := A) Iₛ hI k) =
      Submodule.span S (Set.range fun i : σ ↦
        AdicCompletion.of Iₛ (KaehlerDifferential k S)
          (KaehlerDifferential.D k S (algebraMap A S (MvPowerSeries.X i)))) := by
  let := Fintype.ofFinite σ
  rw [← range_completedDifferentialBaseChange_eq_ker_of_finiteType_fiber (k := k) Iₛ hI]
  let f := completedDifferentialBaseChange (R := A) Iₛ k
  let B := powerSeriesBaseChangeCompletedDifferentialBasis (σ := σ) (k := k) (S := S)
  have hf : f = B.constr ℕ (fun i ↦ f (B i)) := (B.constr_self ℕ f).symm
  change LinearMap.range f = _
  rw [hf, Module.Basis.constr_range]
  congr 1
  funext i
  simp [f, B, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

end BaseChange

section Powers

variable {σ k S : Type*} [Finite σ] [CommRing k] [CommRing S]
  [Algebra (MvPowerSeries σ k) S] [Algebra k S] [IsScalarTower k (MvPowerSeries σ k) S]
  [Algebra.EssFiniteType (MvPowerSeries σ k) S] [IsNoetherianRing S] [IsLocalRing S]
  {p : ℕ} [CharP S p]
local notation "A" => MvPowerSeries σ k
local notation "Iₛ" => Ideal.map (algebraMap A S)
  (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k))))
variable [IsAdicComplete
    ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S)) S]
  [Algebra.EssFiniteType k
    (S ⧸ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S))]

/-- p乗への評価では、完備微分の係数制限の核は零。 -/
theorem ker_completedDifferentialRestriction_of_powerSeries_powers
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    LinearMap.ker (completedDifferentialRestriction (R := A) Iₛ hI k) = ⊥ := by
  rw [ker_powerSeriesCompletedDifferentialRestriction_eq_span hI]
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, rfl⟩
  change AdicCompletion.of Iₛ (KaehlerDifferential k S)
    (KaehlerDifferential.D k S (algebraMap A S (MvPowerSeries.X i))) = 0
  rw [hX i]
  have hd : KaehlerDifferential.D k S (z i ^ p) = 0 :=
    derivation_pow_char_eq_zero p (KaehlerDifferential.D k S) (z i)
  rw [hd, map_zero]

/-- p乗への評価で、係数環上の完備微分と冪級数環上の通常相対微分を同定する。 -/
def powerSeriesPowersCompletedDifferentialEquiv
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    AdicCompletion Iₛ (KaehlerDifferential k S) ≃ₗ[S] KaehlerDifferential A S :=
  LinearEquiv.ofBijective (completedDifferentialRestriction (R := A) Iₛ hI k)
    ⟨(LinearMap.ker_eq_bot).mp
      (ker_completedDifferentialRestriction_of_powerSeries_powers z hX hI),
      completedDifferentialRestriction_surjective (R := A) Iₛ hI k⟩

@[simp] theorem powerSeriesPowersCompletedDifferentialEquiv_of_D
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) (s : S) :
    powerSeriesPowersCompletedDifferentialEquiv z hX hI
      (AdicCompletion.of Iₛ (KaehlerDifferential k S) (KaehlerDifferential.D k S s)) =
        KaehlerDifferential.D A S s :=
  completedDifferentialRestriction_D (R := A) Iₛ hI k s

end Powers

end SerrePositivity
