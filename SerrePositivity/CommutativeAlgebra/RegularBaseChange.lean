module

public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 非零因子の平坦基底変更と有界ねじれ

平坦な代数による基底変更は、加群上の非零因子を保存する。
ここではテンソル積における左代数の作用を明示し、`p` 正則性から
有界 `p` 冪ねじれ条件を指数零で導く。具体的な塔の平坦性は仮定から導かない。
-/

@[expose] public section
universe u
open scoped TensorProduct

namespace SerrePositivity

/-- D 上の非零因子は、平坦 A 代数 R による基底変更後も非零因子。
テンソル積上では R の左作用と、`g` の R 内の標準像を用いる。 -/
theorem isSMulRegular_tensorProduct_of_flat
    (A R D : Type u) [CommRing A] [CommRing R] [CommRing D]
    [Algebra A R] [Algebra A D] [Module.Flat A R]
    (g : A) (hg : IsSMulRegular D (algebraMap A D g)) :
    IsSMulRegular (R ⊗[A] D) (algebraMap A R g) := by
  have hg' : IsSMulRegular D g := by
    change Function.Injective (fun d : D ↦ g • d)
    change Function.Injective (fun d : D ↦ algebraMap A D g * d) at hg
    simpa only [Algebra.smul_def] using hg
  have hbase : IsSMulRegular (R ⊗[A] D) g := hg'.lTensor R
  change Function.Injective (fun x : R ⊗[A] D ↦ g • x) at hbase
  change Function.Injective (fun x : R ⊗[A] D ↦ algebraMap A R g • x)
  simpa only [IsScalarTower.algebraMap_smul] using hbase

/-- 正則な `p` について、`p` の任意の冪で消える元は零。
有界ねじれ条件では指数 `N=0` を取ることができる。 -/
theorem exists_pow_torsion_bound_of_isSMulRegular
    (S : Type u) [CommRing S] (p : ℕ) (hp : IsSMulRegular S (p : S)) :
    ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0 := by
  refine ⟨0, ?_⟩
  intro n s hs
  have hz : s = 0 := (hp.pow n).right_eq_zero_of_smul (by simpa [smul_eq_mul] using hs)
  simp [hz]

end SerrePositivity
