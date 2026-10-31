module

public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import SerrePositivity.PerfectComplex.Free.K0
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Theorem 3.1（台つき有理 K 理論の降下）の帰結

## 概要

論文 Theorem 3.1 は、有限群 `G` が幾何ファイバーで推移的に作用する有限射 `Spec T → Spec A` について、
台つき K 理論の有理化が `G` 不変部分への降下をみたすことを主張する。このプロジェクトで使うのは
その `K₀` のレベルの帰結 (3.2)「`K_0^J(A) ⊗ ℚ → (K_0^J(T) ⊗ ℚ)^G` は全射」だけである。このファイルは
それを `H = A`（離散・可換）、`J = m_A` の場合に、`sorry` 付きの定理 `theorem_3_1_K0` として置く
（保留した K 理論）。

## 定式化

`⊗ ℚ` を避けて整数版で書く：`K₀(T)` の `G` 不変な元 `y` には、正の整数 `n` と `x ∈ K₀(A)` があって
`n • y = K0.map x`。(3.2) からこの形が出る：`y ⊗ 1` の原像 `x ⊗ (1/m)` をとれば `m • y - x` の像は
ねじれ元なので、さらに適当な倍数で消える。逆に §5 で要るのはこの形だけである
（`Paper/Section5/Positivity.lean`）。

## 設定

論文より狭く、`A` は Noether 局所環で剰余標数 `p > 0`、`z` はパラメータ系（`√(z) = m_A`）とする。
`A` が `ℤ_(p)` 代数であること、`J ∋ p` であることはこの設定から自動（`J = (z) + (p)` と `(z)` は
同じ台）。`T` は `A` 上有限、有限群 `G` が `A` 上 `T` に作用し、`Spec T → Spec A` は全射で、`G` は
幾何ファイバーで推移的（`CommutativeAlgebra/GeometricFiber.lean`）。

証明は Theorem 3.1（Land–Tamme の truncating invariant の cdh 降下、有限忠実平坦被覆の Čech 降下、
幾何的な軌道の議論）によるもので、このプロジェクトの範囲外として `sorry` のまま置く。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **Theorem 3.1 の `K₀` レベルの帰結**（層 2、未証明）：上の設定で、`K₀^{(z)}(T)` の `G` 不変な元
`y`（`g • y = y`、作用は `K0.lean` の `instDistribMulAction`）には、正の整数 `n` と `x ∈ K₀^{(z)}(A)`
があって `n • y = K0.map (algebraMap A T) x`。仮定 `_hz`、`_hsurj`、`_htrans` は結論の型には現れないが
定理の成立に必要な条件なので、引数として残している。 -/
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
