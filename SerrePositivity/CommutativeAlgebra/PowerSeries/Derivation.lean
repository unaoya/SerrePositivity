module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.RingTheory.Derivation
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-! # 冪級数環の導分

概要：有限変数の冪級数環 `A = R[[X]]` から `A` 加群 `M` への導分について
- 変数の像 `a : σ → M` から、偏微分の和 `Σ ∂_i f • a_i` で導分を作る（`powerSeriesDerivation`）。
- `M` が `(X)` 進分離なら、導分は変数の像で決まる。したがって変数の像を指定した導分が一意に存在する。
- 同じく、`Ω_{A/R}` から分離な加群への `A` 線形写像は `dX_i` の像で決まる。
方針：一意性は位相を使わない。導分は `(X)^{N+1}` を `(X)^N M` に送る（`derivation_mem_pow_smul`）ので、
全次数 `N + 1` での切り捨て（多項式）との差を見れば、二つの導分の差は全ての `N` で `(X)^N M` に入る。
多項式の上では Leibniz 則から一致する。
規約：係数環に位相を入れない。位相的な版（連続導分）は `PowerSeries/ContinuousDerivation`。
使われ方：冪級数環の完備微分の計算（`PowerSeries/Differential`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M] [IsScalarTower R (MvPowerSeries σ R) M]

section Construction

variable [Fintype σ]

/-- 変数の指定像から、偏微分の有限和で導分を作る。 -/
def powerSeriesDerivation (a : σ → M) : Derivation R (MvPowerSeries σ R) M :=
  ∑ i, (LinearMap.toSpanSingleton (MvPowerSeries σ R) M (a i)).compDer
    (MvPowerSeries.pderiv (R := R) i)

theorem powerSeriesDerivation_apply (a : σ → M) (f : MvPowerSeries σ R) :
    powerSeriesDerivation (R := R) a f = ∑ i, MvPowerSeries.pderiv (R := R) i f • a i := by
  simp [powerSeriesDerivation]

@[simp] theorem powerSeriesDerivation_X (a : σ → M) (j : σ) :
    powerSeriesDerivation (R := R) a (MvPowerSeries.X j) = a j := by
  classical
  rw [powerSeriesDerivation_apply]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply]

/-- 偏微分を並べた、有限自由加群 `A^σ` への導分。 -/
def powerSeriesContinuousDifferential :
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

end Construction

section Ext

variable [Finite σ]
  [IsHausdorff (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) M]

omit [IsScalarTower R (MvPowerSeries σ R) M] in
/-- 分離な加群への導分は、変数の像で決まる。位相・完備性は使わない。 -/
theorem powerSeries_derivation_ext_of_isHausdorff
    (δ₁ δ₂ : Derivation R (MvPowerSeries σ R) M)
    (hX : ∀ i, δ₁ (MvPowerSeries.X i) = δ₂ (MvPowerSeries.X i)) : δ₁ = δ₂ := by
  classical
  let := Fintype.ofFinite σ
  let J := Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
  have hpoly : ∀ f : MvPolynomial σ R, δ₁ (f : MvPowerSeries σ R) = δ₂ f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.coe_C]
      change δ₁ (algebraMap R (MvPowerSeries σ R) r) = δ₂ (algebraMap R (MvPowerSeries σ R) r)
      rw [δ₁.map_algebraMap, δ₂.map_algebraMap]
    | add f g hf hg =>
      simpa only [MvPolynomial.coe_add, map_add] using congrArg₂ (· + ·) hf hg
    | mul_X f i hf =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, hf, hX]
  ext f
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (inferInstance : IsHausdorff J M)
  intro N
  rw [SModEq.zero]
  set p : MvPolynomial σ R := MvPowerSeries.truncTotal (N + 1) f
  have hr : f - (p : MvPowerSeries σ R) ∈ J ^ (N + 1) := by
    apply (mem_powerSeries_variables_pow_iff (N + 1) _).mpr
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hα, sub_self]
  have hsplit : δ₁ f - δ₂ f = δ₁ (f - p) - δ₂ (f - p) := by
    rw [map_sub, map_sub, hpoly p]
    abel
  rw [hsplit]
  exact Submodule.sub_mem _ (derivation_mem_pow_smul δ₁ J N hr)
    (derivation_mem_pow_smul δ₂ J N hr)

/-- 分離な加群には、変数の像を指定した導分が一意に存在する。 -/
theorem existsUnique_powerSeriesDerivation_of_isHausdorff (a : σ → M) :
    ∃! δ : Derivation R (MvPowerSeries σ R) M, ∀ i, δ (MvPowerSeries.X i) = a i := by
  let := Fintype.ofFinite σ
  exact ⟨powerSeriesDerivation a, powerSeriesDerivation_X a, fun δ hδ ↦
    powerSeries_derivation_ext_of_isHausdorff δ _ fun i ↦
      (hδ i).trans (powerSeriesDerivation_X a i).symm⟩

/-- 分離な加群への `Ω_{A/R}` からの線形写像は、`dX_i` の像で決まる。 -/
theorem powerSeries_kaehler_linearMap_ext_of_isHausdorff
    (f g : KaehlerDifferential R (MvPowerSeries σ R) →ₗ[MvPowerSeries σ R] M)
    (hX : ∀ i, f (KaehlerDifferential.D R _ (MvPowerSeries.X i)) =
      g (KaehlerDifferential.D R _ (MvPowerSeries.X i))) : f = g := by
  apply Derivation.liftKaehlerDifferential_unique
  exact powerSeries_derivation_ext_of_isHausdorff _ _ hX

end Ext

end SerrePositivity
