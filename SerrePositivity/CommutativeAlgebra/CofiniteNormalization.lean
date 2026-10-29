module

public import SerrePositivity.CommutativeAlgebra.FractionDifferential
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Differential
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.EqualCharacteristicNormalization
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficient
public import SerrePositivity.CommutativeAlgebra.CofiniteFraction
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization

/-! # 固定した正規化での中間係数体上の完備微分の次元

概要：同標数 `p` の完備 Noether 局所整域 `D`、係数体 `K → D`（剰余体へ全射）、準素パラメータ `z_1, …, z_h` を取る。
十分大きな有限集合 `f` について、`K_f` 上の極大イデアル進の完備微分の生成点での次元は `h + |f|`
（`IsPBasis.exists_completed_finrank_of_parameters`）。
方針：
1. `K_e[[X]] → D`（`X_i ↦ z_i^p`）について、`K_e` 上の完備微分を相対微分 `Ω_{D/K_e[[X]]}` と同定する
   （`PowerSeries/Differential` の `p` 乗評価の同型）。極大イデアル進へは完備化のイデアルの取り替えで移る。
2. 分数体へ移すと `Ω_{Frac D/Frac K_e[[X]]}`。これは `K[[T]] → D` の正規化を経て、`CofiniteFraction` の
   部分体の族 `F_f` 上の微分になる。
3. 十分大きな `f` 以降、`Frac D` と `Frac K[[T]]` で次元が等しく、後者は微分基底から `h + |f|`。
規約：正規化 `K[[T]] → D` は G6 の通常の有限正規化を使い、分離性は仮定しない。
使われ方：Cohen–Gabber の係数切断の取り替え（`PBasisIndependentCoefficientPerturbation`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Comparison

universe u
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [IsLocalRing D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
  {σ : Type*} (e : Finset ι)
  [Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) D]
local notation "E" => pBasisCofiniteField (p := p) b e
local notation "A" => MvPowerSeries σ E
local notation "Iₛ" => Ideal.map (algebraMap A D)
  (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := E))))

/-- 同じ評価の変数イデアルの像は、p乗パラメータの生成イデアルとして準素。 -/
theorem radical_cofinitePowerSeries_variableImage
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    (Iₛ).radical = IsLocalRing.maximalIdeal D := by
  rw [map_powerSeries_variables_eq_span (algebraMap A D) (fun i ↦ z i ^ p) hX]
  exact (radical_span_powers z (fun _ ↦ p) (fun _ ↦ (Fact.out : p.Prime).pos)).trans hprimary

variable [Algebra K D] [Finite σ] [IsNoetherianRing D]
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  [IsScalarTower (pBasisCofiniteField (p := p) b e)
    (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) D]
  [Module.Finite (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) D]

/-- 準素閉ファイバーの有限性を確認して、κ_e上の完備微分を同じ評価の相対微分へ同定する。 -/
def IsPBasis.cofiniteCompletedDifferentialEquiv
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    AdicCompletion Iₛ (KaehlerDifferential E D) ≃ₗ[D] KaehlerDifferential A D := by
  have hrad := radical_cofinitePowerSeries_variableImage e z hX hprimary
  have hI : Iₛ ≤ IsLocalRing.maximalIdeal D := by rw [← hrad]; exact Ideal.le_radical
  let : CharP D p := charP_of_injective_algebraMap (algebraMap K D).injective p
  let : IsAdicComplete Iₛ D := isAdicComplete_finite_of_le_maximalIdeal Iₛ hI
  let : Module.Finite E (D ⧸ Iₛ) :=
    hb.moduleFinite_primaryQuotient_cofiniteField e hres Iₛ hrad
  exact powerSeriesPowersCompletedDifferentialEquiv z hX hI

@[simp] theorem IsPBasis.cofiniteCompletedDifferentialEquiv_of_D
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) (d : D) :
    hb.cofiniteCompletedDifferentialEquiv e hres z hX hprimary
      (AdicCompletion.of Iₛ (KaehlerDifferential E D) (KaehlerDifferential.D E D d)) =
        KaehlerDifferential.D A D d := by
  simp [IsPBasis.cofiniteCompletedDifferentialEquiv]

/-- 極大イデアル進の完備微分を、同じp乗評価の通常相対微分へ同定する。
二つの完備微分の有限性から、相手のイデアルについての完備性を確認する。 -/
def IsPBasis.cofiniteMaximalCompletedDifferentialEquiv
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    AdicCompletion (IsLocalRing.maximalIdeal D) (KaehlerDifferential E D) ≃ₗ[D]
      KaehlerDifferential A D := by
  let C := AdicCompletion Iₛ (KaehlerDifferential E D)
  let M := AdicCompletion (IsLocalRing.maximalIdeal D) (KaehlerDifferential E D)
  have hrad := radical_cofinitePowerSeries_variableImage e z hX hprimary
  have hI : Iₛ ≤ IsLocalRing.maximalIdeal D := by rw [← hrad]; exact Ideal.le_radical
  let : IsAdicComplete Iₛ D := isAdicComplete_finite_of_le_maximalIdeal Iₛ hI
  let : Module.Finite D C :=
    Module.Finite.equiv (hb.cofiniteCompletedDifferentialEquiv e hres z hX hprimary).symm
  let : Module.Finite D M := hb.moduleFinite_completedKaehler_cofiniteField e hres
    (IsLocalRing.maximalIdeal D) (IsLocalRing.maximalIdeal.isMaximal D).isPrime.radical
  let : IsAdicComplete Iₛ M := isAdicComplete_finite_of_ideal_complete Iₛ hI M
  let : IsAdicComplete (IsLocalRing.maximalIdeal D) C :=
    isAdicComplete_finite_of_ideal_complete (IsLocalRing.maximalIdeal D) le_rfl C
  exact (adicCompletionChangeIdealEquiv (IsLocalRing.maximalIdeal D) Iₛ
    (IsLocalRing.maximalIdeal D).fg_of_isNoetherianRing (Iₛ).fg_of_isNoetherianRing).trans
    (hb.cofiniteCompletedDifferentialEquiv e hres z hX hprimary)

@[simp] theorem IsPBasis.cofiniteMaximalCompletedDifferentialEquiv_of_D
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) (d : D) :
    hb.cofiniteMaximalCompletedDifferentialEquiv e hres z hX hprimary
      (AdicCompletion.of (IsLocalRing.maximalIdeal D) (KaehlerDifferential E D)
        (KaehlerDifferential.D E D d)) = KaehlerDifferential.D A D d := by
  simp [IsPBasis.cofiniteMaximalCompletedDifferentialEquiv]

variable (Q L : Type*) [Field Q] [Field L]
  [Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) Q]
  [IsFractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) Q]
  [Algebra D L] [IsFractionRing D L]
  [Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) L] [Algebra Q L]
  [IsScalarTower (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) D L]
  [IsScalarTower (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) Q L]

/-- 極大イデアル進のκ_e上の完備微分を、同じ評価の分数体の通常微分へ同定する。 -/
def IsPBasis.cofiniteMaximalCompletedFractionDifferentialEquiv
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    L ⊗[D] AdicCompletion (IsLocalRing.maximalIdeal D) (KaehlerDifferential E D) ≃ₗ[L]
      KaehlerDifferential Q L :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (hb.cofiniteMaximalCompletedDifferentialEquiv e hres z hX hprimary)).trans
    (fractionDifferentialEquiv A D Q L)

@[simp] theorem IsPBasis.cofiniteMaximalCompletedFractionDifferentialEquiv_tmul_of_D
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D)
    (l : L) (d : D) :
    hb.cofiniteMaximalCompletedFractionDifferentialEquiv e Q L hres z hX hprimary
      (l ⊗ₜ[D] AdicCompletion.of (IsLocalRing.maximalIdeal D) (KaehlerDifferential E D)
        (KaehlerDifferential.D E D d)) =
      l • KaehlerDifferential.D Q L (algebraMap D L d) := by
  simp [IsPBasis.cofiniteMaximalCompletedFractionDifferentialEquiv]

/-- 極大イデアル進の完備微分の生成点の次元も、同じ分数体の通常微分の次元。 -/
theorem IsPBasis.finrank_cofiniteMaximalCompletedFractionDifferential
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    Module.finrank L (L ⊗[D] AdicCompletion (IsLocalRing.maximalIdeal D)
      (KaehlerDifferential E D)) = Module.finrank L (KaehlerDifferential Q L) :=
  (hb.cofiniteMaximalCompletedFractionDifferentialEquiv e Q L hres z hX hprimary).finrank_eq

end Comparison

section Rank

universe u
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι σ : Type*} [Finite σ] {b : ι → K}

/-- 通常有限正規化を固定すると、十分大きい有限集合以降で完備微分の階数が
元の冪級数分数体の相対微分の階数に一致する。 -/
theorem IsPBasis.exists_cofiniteNormalization_completed_rank_stable
    (hb : IsPBasis K p b)
    (F : MvPowerSeries σ K →+* D) (hF : Function.Injective F) (hfin : F.Finite)
    (hC : ∀ a, F (MvPowerSeries.C a) = algebraMap K D a)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (inferInstance : Algebra
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))).toSMul
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) =
      Module.finrank (FractionRing (MvPowerSeries σ K)) (KaehlerDifferential
        (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
        (FractionRing (MvPowerSeries σ K))) := by
  let K₀ := FractionRing (MvPowerSeries σ K)
  let L := FractionRing D
  let : Algebra (MvPowerSeries σ K) D := F.toAlgebra
  have : FaithfulSMul (MvPowerSeries σ K) D :=
    (faithfulSMul_iff_algebraMap_injective _ D).mpr hF
  let : Module.Finite (MvPowerSeries σ K) D := hfin
  let : Algebra K₀ L := FractionRing.liftAlgebra _ L
  let : Module.Finite K₀ L := finiteDimensional_fractionRing_of_finite (MvPowerSeries σ K) D K₀ L
  let : CharP D p := charP_of_injective_algebraMap (algebraMap K D).injective p
  let : CharP L p := charP_of_injective_algebraMap (IsFractionRing.injective D L) p
  obtain ⟨e, he⟩ := hb.exists_cofiniteFractionField_rank_stable (σ := σ) (L := L)
  refine ⟨e, ?_⟩
  intro f hf
  let E := pBasisCofiniteField (p := p) b f
  let A := MvPowerSeries σ E
  let Q := FractionRing A
  let ψ : A →+* MvPowerSeries σ K := powerSeriesExpandMap p (Fact.out : p.Prime).pos
  let φ : Q →+* K₀ := powerSeriesFractionMap p (Fact.out : p.Prime).pos
  let : Algebra Q K₀ := φ.toAlgebra
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  let : Algebra Q L := ((algebraMap K₀ L).comp φ).toAlgebra
  let : Module Q L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra Q L)
  let : SMul Q L := (inferInstance : Algebra Q L).toSMul
  let : Algebra A D := (F.comp ψ).toAlgebra
  let : Module A D := @Algebra.toModule _ _ _ _ (inferInstance : Algebra A D)
  let : SMul A D := (inferInstance : Algebra A D).toSMul
  let : Module.Finite A D := hfin.comp (hb.powerSeries_cofinite_expand_injective_finite f).2
  let : IsScalarTower E A D := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    change algebraMap E D a = F (ψ (MvPowerSeries.C a))
    rw [powerSeriesExpandMap_C, hC]
    exact IsScalarTower.algebraMap_apply E K D a)
  have hXp : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p := by
    intro i
    change F (ψ (MvPowerSeries.X i)) = z i ^ p
    rw [powerSeriesExpandMap_X, map_pow, hX]
  let : Algebra A L := ((algebraMap D L).comp (F.comp ψ)).toAlgebra
  let : Module A L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra A L)
  let : SMul A L := (inferInstance : Algebra A L).toSMul
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A Q L := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    change algebraMap D L (F (ψ a)) = algebraMap K₀ L
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos (algebraMap A Q a))
    rw [powerSeriesFractionMap_algebraMap,
      ← IsScalarTower.algebraMap_apply (MvPowerSeries σ K) K₀ L,
      IsScalarTower.algebraMap_apply (MvPowerSeries σ K) D L]
    rfl)
  exact (hb.finrank_cofiniteMaximalCompletedFractionDifferential
    f Q L hres z hXp hprimary).trans (he f hf)

end Rank

section Dimension

universe u
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι σ : Type*} [Finite σ] {b : ι → K}

/-- 通常有限正規化に対し、十分大きいfでκ_f上の完備微分の生成点の次元はh+|f|。 -/
theorem IsPBasis.exists_cofiniteNormalization_completed_finrank
    (hb : IsPBasis K p b)
    (F : MvPowerSeries σ K →+* D) (hF : Function.Injective F) (hfin : F.Finite)
    (hC : ∀ a, F (MvPowerSeries.C a) = algebraMap K D a)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) =
        Nat.card σ + f.card := by
  let := Fintype.ofFinite σ
  obtain ⟨e, he⟩ := hb.exists_cofiniteNormalization_completed_rank_stable
    F hF hfin hC hres z hX hprimary
  refine ⟨e, ?_⟩
  intro f hf
  have h := (he f hf).trans (hb.finrank_cofiniteFractionDifferential (σ := σ) f)
  simpa only [Nat.card_eq_fintype_card] using h

/-- 係数写像とh個の準素パラメータから通常有限正規化を構成し、完備微分の次元を計算する。
分離的正規化の存在は入力に要求しない。 -/
theorem IsPBasis.exists_completed_finrank_of_parameters
    (hb : IsPBasis K p b) {h : ℕ} (hdim : ringKrullDim D = h)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : Fin h → D) (hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) = h + f.card := by
  obtain ⟨F, hF, hfin, _, hC, hX⟩ := exists_injective_finite_powerSeries_map_of_parameters
    (algebraMap K D) hres hdim z hzm hprimary
  simpa only [Nat.card_fin] using
    hb.exists_cofiniteNormalization_completed_finrank F hF hfin hC hres z hX hprimary

end Dimension

end SerrePositivity
