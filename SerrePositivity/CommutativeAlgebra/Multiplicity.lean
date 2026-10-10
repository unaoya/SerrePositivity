module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# パラメータ系

## 概要

論文 §2（Lemma 2.2、Theorem 2.5）の設定を書くのに要る概念を定義する。

- `dimToNat`：`WithBot ℕ∞` 値の次元を自然数に落とす。
- `IsSystemOfParameters D z`：`z = (z_1, …, z_h)` が局所環 `D` のパラメータ系であること。
  すなわち `h = dim D` で、`(z)` が `m_D` 準素（根基が `m_D`）。

Hilbert–Samuel 重複度 `e(I, M)` は `CommutativeAlgebra/HilbertSamuel.lean` で、Samuel 関数
`n ↦ ℓ(M/I^n M)` を表す多項式の最高次係数として定義する（以前ここにあった極限の式による定義は
2026-10-10 に置き換えた）。
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
パラメータ系になる、`Paper/Section2/Lemma2_2.lean`）に使う。 -/
def IsSystemOfParameters [IsLocalRing D] {h : ℕ} (z : Fin h → D) : Prop :=
  ringKrullDim D = h ∧ (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D

end SerrePositivity
