module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
概要：形式関数に使う長完全列の図式追跡と、核の評価からの単射性。
方針：連結写像の自然性と、Rees 側の核を消す遷移写像を使う。
規約：コホモロジーの構成から独立な、線形写像の入力として述べる。
使われ方：射影 Čech 版の像の安定化と、BST13 Lemma 3.9 の正次数の単射性。
原典 Stacks 30.20.4(1),(3) の Hⁱ の主張に渡す、線形図式の補題である。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R H Q₀ Q₁ K₀ K₁ J : Type*} [CommRing R]
variable [AddCommGroup H] [Module R H]
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁]
variable [AddCommGroup J] [Module R J]

/-- 十分先の核が遷移写像で零になれば、厚化のコホモロジーの像が安定する。 -/
theorem formalFunctions_range_eq_of_kernel_killed
    (u₀ : H →ₗ[R] Q₀) (u₁ : H →ₗ[R] Q₁)
    (δ₀ : Q₀ →ₗ[R] K₀) (δ₁ : Q₁ →ₗ[R] K₁) (w₁ : K₁ →ₗ[R] J)
    (q : Q₁ →ₗ[R] Q₀) (k : K₁ →ₗ[R] K₀)
    (h₀ : Function.Exact u₀ δ₀) (h₁ : Function.Exact δ₁ w₁)
    (hu : q.comp u₁ = u₀) (hδ : δ₀.comp q = k.comp δ₁)
    (hkill : LinearMap.ker w₁ ≤ LinearMap.ker k) :
    LinearMap.range q = LinearMap.range u₀ := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    apply (h₀ _).mp
    have hy : δ₁ y ∈ LinearMap.ker w₁ := (h₁ _).mpr ⟨y, rfl⟩
    calc
      δ₀ (q y) = k (δ₁ y) := DFunLike.congr_fun hδ y
      _ = 0 := hkill hy
  · rintro _ ⟨h, rfl⟩
    exact ⟨u₁ h, DFunLike.congr_fun hu h⟩

section Injectivity

variable {M : Type*} [AddCommGroup M] [Module R M]
variable (I : Ideal R) {Q : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]

/-- 核の I 進評価と I の冪による零化から、十分厚い商への単射性が従う。 -/
theorem formalFunctions_eventually_injective_of_kernel_bound
    (u : ∀ n, M →ₗ[R] Q n) (c k : ℕ)
    (hker : ∀ n, c ≤ n → LinearMap.ker (u n) ≤ I ^ (n - c) • (⊤ : Submodule R M))
    (hkill : I ^ k • (⊤ : Submodule R M) = ⊥) :
    ∀ n, c + k ≤ n → Function.Injective (u n) := by
  intro n hn
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  calc
    LinearMap.ker (u n) ≤ I ^ (n - c) • (⊤ : Submodule R M) := hker n (by omega)
    _ ≤ I ^ k • (⊤ : Submodule R M) :=
      Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
    _ = ⊥ := hkill

end Injectivity

end SerrePositivity.AlgebraicGeometry
