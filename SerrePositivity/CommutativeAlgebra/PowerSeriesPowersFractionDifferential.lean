module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesPowersCompletedDifferential
public import SerrePositivity.CommutativeAlgebra.FractionDifferential

/-! # p乗への冪級数評価に沿う完備微分の分数体比較

係数環上の完備微分を、同じ評価の分数体拡大の通常相対微分へ同定する。
元の微分とその完備化・局所化の像を同じ写像で追う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {σ k S : Type*} [Finite σ] [CommRing k] [CommRing S]
  [Algebra (MvPowerSeries σ k) S] [Algebra k S] [IsScalarTower k (MvPowerSeries σ k) S]
  [Algebra.EssFiniteType (MvPowerSeries σ k) S] [IsNoetherianRing S] [IsLocalRing S]
  {p : ℕ} [CharP S p]
  [IsAdicComplete
    ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S)) S]
  [Algebra.EssFiniteType k
    (S ⧸ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map
      (algebraMap (MvPowerSeries σ k) S))]
local notation "A" => MvPowerSeries σ k
local notation "Iₛ" => Ideal.map (algebraMap A S)
  (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k))))
variable (K L : Type*) [Field K] [Field L]
  [Algebra (MvPowerSeries σ k) K] [IsFractionRing (MvPowerSeries σ k) K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra (MvPowerSeries σ k) L] [Algebra K L]
  [IsScalarTower (MvPowerSeries σ k) S L] [IsScalarTower (MvPowerSeries σ k) K L]

/-- p乗への評価について、係数環上の完備微分を分数体の通常微分へ同定する。 -/
def powerSeriesPowersFractionDifferentialEquiv
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    L ⊗[S] AdicCompletion Iₛ (KaehlerDifferential k S) ≃ₗ[L] KaehlerDifferential K L :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (powerSeriesPowersCompletedDifferentialEquiv z hX hI)).trans
    (fractionDifferentialEquiv A S K L)

@[simp] theorem powerSeriesPowersFractionDifferentialEquiv_tmul_of_D
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) (l : L) (s : S) :
    powerSeriesPowersFractionDifferentialEquiv K L z hX hI
      (l ⊗ₜ[S] AdicCompletion.of Iₛ (KaehlerDifferential k S) (KaehlerDifferential.D k S s)) =
        l • KaehlerDifferential.D K L (algebraMap S L s) := by
  simp [powerSeriesPowersFractionDifferentialEquiv]

/-- 自然な比較同型から、同じ評価についての分数体上の次元等号を得る。 -/
theorem finrank_powerSeriesPowers_completedDifferential
    (z : σ → S) (hX : ∀ i, algebraMap A S (MvPowerSeries.X i) = z i ^ p)
    (hI : Iₛ ≤ IsLocalRing.maximalIdeal S) :
    Module.finrank L (L ⊗[S] AdicCompletion Iₛ (KaehlerDifferential k S)) =
      Module.finrank L (KaehlerDifferential K L) :=
  (powerSeriesPowersFractionDifferentialEquiv K L z hX hI).finrank_eq

end SerrePositivity
