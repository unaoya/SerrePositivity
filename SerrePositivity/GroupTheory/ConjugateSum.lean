module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-! # 有限群の作用に関する加法的評価の共役和

アーベル群の準同型 `f : K →+ K'` と有限群の `K'` への作用を考える。
二つの実数値の加法的評価が `f` の像で一致し、不変元の正の整数倍が
その像へ降下すれば、両評価の共役和は一致する。
評価の群不変性は要求しない。Euler 評価への適用は `CategoryTheory/EulerComparison` に置く。
-/

@[expose] public section

namespace SerrePositivity

/-- **共役和の一致**：`φ ∘ f = ψ ∘ f`（`h1`）かつ `G` 不変な元の正の倍数が `f` の像に入る（`h2`）なら、
任意の `y` で `Σ_g φ(g • y) = Σ_g ψ(g • y)`。 -/
theorem conjSum_eq {K K' : Type*} [AddCommGroup K] [AddCommGroup K'] (f : K →+ K')
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G K']
    (φ ψ : K' →+ ℝ) (h1 : ∀ x, φ (f x) = ψ (f x))
    (h2 : ∀ y : K', (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : K') : ∑ g : G, φ (g • y) = ∑ g : G, ψ (g • y) := by
  set s := ∑ g : G, g • y with hs
  have hinv : ∀ h : G, h • s = s := by
    intro h
    rw [hs, Finset.smul_sum]
    simp_rw [smul_smul]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g ↦ rfl)
  obtain ⟨n, x, hn, hx⟩ := h2 s hinv
  have hφ : (n : ℝ) * ∑ g : G, φ (g • y) = φ (f x) := by
    rw [← hx, map_nsmul, nsmul_eq_mul, hs, map_sum]
  have hψ : (n : ℝ) * ∑ g : G, ψ (g • y) = ψ (f x) := by
    rw [← hx, map_nsmul, nsmul_eq_mul, hs, map_sum]
  have : (n : ℝ) * ∑ g : G, φ (g • y) = (n : ℝ) * ∑ g : G, ψ (g • y) := by
    rw [hφ, hψ, h1]
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') this

end SerrePositivity

end
