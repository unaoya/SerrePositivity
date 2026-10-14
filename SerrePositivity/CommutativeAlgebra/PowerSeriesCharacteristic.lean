module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.CharP.Algebra

/-! # 冪級数環の標数

定数係数の埋め込みの単射性から標数を移す。変数の有限性や整域性は不要。
-/

public section
namespace SerrePositivity

/-- 定数の埋め込みは単射なので、冪級数環の標数は係数環と同じ。 -/
instance charP_mvPowerSeries (σ R : Type*) [CommSemiring R] (p : ℕ) [CharP R p] :
    CharP (MvPowerSeries σ R) p :=
  charP_of_injective_algebraMap MvPowerSeries.C_injective p

end SerrePositivity
