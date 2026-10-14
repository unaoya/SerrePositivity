module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # 整域係数の冪級数環の整域性 -/

public section
namespace SerrePositivity

/-- 整域係数の多変数冪級数環は整域。Mathlibの零因子なしのインスタンスを使う。 -/
instance isDomain_mvPowerSeries (σ R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (MvPowerSeries σ R) := NoZeroDivisors.to_isDomain _

end SerrePositivity
