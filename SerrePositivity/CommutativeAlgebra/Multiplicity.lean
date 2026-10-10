module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# パラメータ系と Hilbert–Samuel 重複度

## 概要

論文 §2（Lemma 2.2、Theorem 2.5）の設定を書くのに要る二つの概念を定義する。どちらも定義だけで、
性質はここでは示さない。

- `IsSystemOfParameters D z`：`z = (z_1, …, z_h)` が局所環 `D` のパラメータ系であること。
  すなわち `h = dim D` で、`(z)` が `m_D` 準素（根基が `m_D`）。
- `hilbertSamuelMultiplicity I M`：Hilbert–Samuel 重複度 `e(I, M) = lim_n d! · ℓ(M / I^n M) / n^d`
  （`d = dim M`）。

## 規約と注意

Hilbert–Samuel 重複度は `Filter.limUnder`（極限が存在すればその値、存在しなければ既定の値）で
定義する。極限の存在、通常の重複度の定義との一致、正値性はここでは証明しない。論文 (2.5) の
「正で有限」は、使う側で仮定として置く（`Inputs/LengthAlgebra.lean`）。`notes/PLAN.md` §1.5 の
とおり、重複度の理論を形式化する代わりに、必要な性質だけを入力として受け取る方針である。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- `WithBot ℕ∞` 値の次元（`ringKrullDim`、`Module.supportDim`）を自然数に落とす。`⊥`（零環・
零加群）と `⊤`（無限次元）は `0` になる。有限次元の場合だけが意味をもつ。 -/
noncomputable def dimToNat (d : WithBot ℕ∞) : ℕ := (d.unbotD 0).toNat

variable (D : Type u) [CommRing D]

/-- `z : Fin h → D` が局所環 `D` のパラメータ系であること：`h = dim D`（Krull 次元）かつ `(z)` が
`m_D` 準素（`√(z) = m_D`）。Lemma 2.2 の正規化基底の条件（`A` の正則パラメータ系が `D` の
パラメータ系になる、`Inputs/LengthAlgebra.lean`）に使う。 -/
def IsSystemOfParameters [IsLocalRing D] {h : ℕ} (z : Fin h → D) : Prop :=
  ringKrullDim D = h ∧ (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D

/-- Hilbert–Samuel 重複度 `e(I, M) = lim_n d! · ℓ_D(M / I^n M) / n^d`（実数値）。`d` は `M` の台の次元
`dim Supp M` を自然数に落としたもの（`dimToNat`）。`M` が有限生成で `I` が `m_D` 準素なら
`ℓ(M / I^n M)` は `n` について `d` 次の多項式で増え、この極限が通常の重複度になる。ここでは
有限生成性や準素性を仮定しない全域的な定義であり、極限の存在、通常の重複度との一致、正値性は
この定義だけからは主張しない（必要な性質は `Inputs/LengthAlgebra.lean` で仮定する）。 -/
noncomputable def hilbertSamuelMultiplicity (I : Ideal D) (M : Type u) [AddCommGroup M]
    [Module D M] : ℝ :=
  let d := dimToNat (Module.supportDim D M)
  Filter.limUnder Filter.atTop fun n : ℕ ↦
    ((d.factorial : ℝ) * ((Module.length D (M ⧸ (I ^ n • (⊤ : Submodule D M)))).toNat : ℝ))
      / (n : ℝ) ^ d

end SerrePositivity
