module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesDifferentialTransitivity
public import SerrePositivity.RingTheory.Derivation

/-! # 変数をp乗へ送る評価の完備微分の比較

完備推移列の核を変数の像の微分で計算し、p乗の微分が零になることを使う。
係数体上の通常の絶対微分の有限生成性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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

end SerrePositivity
