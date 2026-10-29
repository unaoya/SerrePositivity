module

public import SerrePositivity.CommutativeAlgebra.AdicPowerSeriesDerivation
public import Mathlib.RingTheory.Kaehler.Basic

/-! # 分離加群への通常の Kähler 微分の普遍性

通常の Ω 自身の有限性は主張しない。変数進分離な終域への写像を変数の微分で決定する。
これを通常の Ω の分離商・完備化の比較の入口にする。
-/

@[expose] public section
namespace SerrePositivity

variable {σ R M : Type*} [Finite σ] [CommRing R]
  [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
  [IsScalarTower R (MvPowerSeries σ R) M]
  [IsHausdorff (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) M]

/-- 分離な終域への通常の微分加群の線形写像は、変数の微分の像で決まる。 -/
theorem powerSeries_kaehler_linearMap_ext_of_isHausdorff
    (f g : KaehlerDifferential R (MvPowerSeries σ R) →ₗ[MvPowerSeries σ R] M)
    (hX : ∀ i, f (KaehlerDifferential.D R _ (MvPowerSeries.X i)) =
      g (KaehlerDifferential.D R _ (MvPowerSeries.X i))) : f = g := by
  apply Derivation.liftKaehlerDifferential_unique
  apply powerSeries_derivation_ext_of_isHausdorff
  exact hX

end SerrePositivity
