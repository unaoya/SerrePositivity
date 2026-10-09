module

public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import SerrePositivity.PerfectComplex.K0Functor
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Theorem 3.1（台つき有理 K 理論の降下）の帰結（層 2）

論文 Theorem 3.1 を `H = A`（離散・可換）、`J = m_A` の場合に、`K₀` のレベルの帰結 (3.2)
「`K_0^J(A) ⊗ ℚ → (K_0^J(T) ⊗ ℚ)^G` は全射」として置く。ここでは `⊗ ℚ` を避けて整数版で書く：
`K₀(T)` の `G` 不変な元 `y` には `n > 0` と `x ∈ K₀(A)` があって `n • y = x` の像。
(3.2) からこの形が出る（`y ⊗ 1` の原像 `x ⊗ (1/m)` をとれば `m • y - x` の像はねじれ）。

設定は論文より狭く、`A` は Noether 局所環で剰余標数 `p > 0`、`z` はパラメータ系（`√(z) = m_A ∋ p`）
とする。`ℤ_(p)` 代数であること、`J ∋ p` はこの設定から自動（`J = (z) + (p)` と `(z)` は同じ台）。
`T` は `A` 上有限、有限群 `G` が `A` 上 `T` に作用し、`Spec T → Spec A` は全射で、
`G` は幾何ファイバーで推移的。

証明は Theorem 3.1（Land–Tamme の truncating invariant の cdh 降下、有限忠実平坦被覆の Čech 降下、
幾何的な軌道の議論）によるもので、ここでは `sorry` のまま置く。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **Theorem 3.1 の `K₀` レベルの帰結**（層 2、未証明）：`G` 不変な類は正の倍数が `K₀(A)` から来る。 -/
theorem theorem_3_1_K0
    (A T : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T] [Algebra A T]
    [Module.Finite A T] (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    {e : ℕ} (z : Fin e → A) (_hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
    (_hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (_htrans : IsGeometricallyTransitive A T G)
    (y : K0Supported T (algebraMap A T ∘ z)) (_hy : ∀ g : G, g • y = y) :
    ∃ (n : ℕ) (x : K0Supported A z), 0 < n ∧ n • y = K0.map (algebraMap A T) x := by
  sorry

end SerrePositivity
