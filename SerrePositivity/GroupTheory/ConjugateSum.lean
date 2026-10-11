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
評価の群不変性は要求しない。`conjSum_eq_of_base_formula` は、二つの評価が基底上の共通の評価の定数倍に
分解する（基底公式）場合の形。Euler 評価への適用は `CategoryTheory/EulerComparison` に置く。
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

/-- **基底公式つきの共役和の一致**：二つの評価が `f` に沿って共通の関数 `χA : K → ℝ` の定数倍に分解する
（`φ (f x) = e₁ * χA x`、`ψ (f x) = e₂ * χA x`、基底公式）とき、`e₁ = e₂` なら `conjSum_eq` の仮定 `h1`
が成り立ち、降下 `h2` から共役和が一致する。二つの実現の比較定理はこの形で使う
（解説の系「基底公式つきの共役和比較」）。 -/
theorem conjSum_eq_of_base_formula {K K' : Type*} [AddCommGroup K] [AddCommGroup K']
    (f : K →+ K') {G : Type*} [Group G] [Fintype G] [DistribMulAction G K']
    (φ ψ : K' →+ ℝ) (χA : K → ℝ) (e₁ e₂ : ℝ)
    (h₁ : ∀ x, φ (f x) = e₁ * χA x) (h₂ : ∀ x, ψ (f x) = e₂ * χA x) (he : e₁ = e₂)
    (h2 : ∀ y : K', (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : K') : ∑ g : G, φ (g • y) = ∑ g : G, ψ (g • y) :=
  conjSum_eq f φ ψ (fun x ↦ by rw [h₁, h₂, he]) h2 y

end SerrePositivity

end
