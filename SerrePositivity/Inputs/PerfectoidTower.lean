module

public import SerrePositivity.CommutativeAlgebra.RootTower.WittPresentation
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # 標準的な根の塔の perfectoid 性（証明済みの互換入口）

CLMST Example 2.4.2 (1) の塔を、有限段の商環と有向極限の `p` 進完備化で表す。
係数環との同型とパラメータの像を明記する。
出典：https://arxiv.org/html/2209.04046v4
-/

public section
universe u
open IsLocalRing
namespace SerrePositivity.Inputs
open Section2

/-- Witt 係数の形式冪級数環で全パラメータの `p` 冪根を添加した塔の完備化は perfectoid。
CLMST Example 2.4.2 (1) の主張を、共通の塔・Frobenius・tilt核の証明から導く。 -/
theorem completedTower_isIntegralPerfectoid
    (A k : Type u) [CommRing A] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  exact completedTower_isIntegralPerfectoid_of_standard_wittPresentation A k p t hpos htp e he

end SerrePositivity.Inputs
