module

public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientNormalization
public import SerrePositivity.CommutativeAlgebra.FractionDifferential
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Differential
public import SerrePositivity.CommutativeAlgebra.AdicCompletionChangeIdeal

/-! # 中間係数体上の完備微分の実際の比較

κ_e[[X]]→D、X_i↦z_i^pについて、閉ファイバーの有限性とイデアル進完備性を確認する。
κ_eの剰余体への全射性は要求せず、元のκとDの共通剰余体を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
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

/-- 同じ有限評価の分数体拡大と、κ_e上の完備微分の生成点での評価を同定する。 -/
def IsPBasis.cofiniteCompletedFractionDifferentialEquiv
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    L ⊗[D] AdicCompletion Iₛ (KaehlerDifferential E D) ≃ₗ[L] KaehlerDifferential Q L :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (hb.cofiniteCompletedDifferentialEquiv e hres z hX hprimary)).trans
    (fractionDifferentialEquiv A D Q L)

@[simp] theorem IsPBasis.cofiniteCompletedFractionDifferentialEquiv_tmul_of_D
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D)
    (l : L) (d : D) :
    hb.cofiniteCompletedFractionDifferentialEquiv e Q L hres z hX hprimary
      (l ⊗ₜ[D] AdicCompletion.of Iₛ (KaehlerDifferential E D) (KaehlerDifferential.D E D d)) =
        l • KaehlerDifferential.D Q L (algebraMap D L d) := by
  simp [IsPBasis.cofiniteCompletedFractionDifferentialEquiv]

omit [Field Q] [Algebra A Q] [IsFractionRing A Q] [Algebra Q L]
  [IsScalarTower A Q L] [IsFractionRing D L] [Algebra A L] [IsScalarTower A D L] in
/-- 生成点での完備微分は実際に有限次元。無限次元のfinrankを0とする規約に依存しない。 -/
theorem IsPBasis.moduleFinite_cofiniteCompletedFractionDifferential
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    Module.Finite L (L ⊗[D] AdicCompletion Iₛ (KaehlerDifferential E D)) := by
  let : Module.Finite D (AdicCompletion Iₛ (KaehlerDifferential E D)) :=
    Module.Finite.equiv (hb.cofiniteCompletedDifferentialEquiv e hres z hX hprimary).symm
  infer_instance

/-- 同じ評価の分数体の通常微分についても有限性を供給する。 -/
theorem IsPBasis.moduleFinite_cofiniteFractionDifferential
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    Module.Finite L (KaehlerDifferential Q L) := by
  let : Module.Finite L (L ⊗[D] AdicCompletion Iₛ (KaehlerDifferential E D)) :=
    hb.moduleFinite_cofiniteCompletedFractionDifferential e L hres z hX hprimary
  exact Module.Finite.equiv (hb.cofiniteCompletedFractionDifferentialEquiv e Q L hres z hX hprimary)

/-- 有限性を伴う、完備微分と通常微分の分数体上の次元の比較。 -/
theorem IsPBasis.finrank_cofiniteCompletedFractionDifferential
    (hb : IsPBasis K p b)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    Module.finrank L (L ⊗[D] AdicCompletion Iₛ (KaehlerDifferential E D)) =
      Module.finrank L (KaehlerDifferential Q L) :=
  (hb.cofiniteCompletedFractionDifferentialEquiv e Q L hres z hX hprimary).finrank_eq

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

end SerrePositivity
