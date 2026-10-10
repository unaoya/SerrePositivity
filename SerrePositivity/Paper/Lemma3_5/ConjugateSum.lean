module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# 共役和の一致（形式的補題、論文 Lemma 3.5 の第 3 段）

アーベル群の準同型 `f : K →+ K'`、`K'` に作用する有限群 `G`、準同型 `φ ψ : K' →+ ℝ` があって
`φ ∘ f = ψ ∘ f` とする。さらに、`K'` の `G` 不変な元は正の倍数が `f` の像に入るとする
（`K_ℚ → (K'_ℚ)^G` の全射性の整数版。Theorem 3.1 の結論 (3.2) から出る）。
このとき任意の `y ∈ K'` で `Σ_g φ(g • y) = Σ_g ψ(g • y)`。

証明：`s = Σ_g g • y` は `G` 不変なので `n • s = f x` となる `n > 0`、`x` がある。
`φ`、`ψ` は準同型なので `n · Σ_g φ(g • y) = φ(f x) = ψ(f x) = n · Σ_g ψ(g • y)`。

`K₀` の具体的な構成とは独立なので先に証明しておく（`notes/lemma-3-5.md`）。
-/

@[expose] public section

namespace SerrePositivity

/-- **共役和の一致**。 -/
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
