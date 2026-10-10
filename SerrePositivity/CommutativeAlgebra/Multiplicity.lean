module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

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

/-- 局所環の自己同型はパラメータ系を保つ。長さ代数上の群作用は必要ない。 -/
theorem IsSystemOfParameters.map_aut [IsLocalRing D] {h : ℕ} {z : Fin h → D}
    (hz : IsSystemOfParameters D z) (σ : D ≃+* D) :
    IsSystemOfParameters D (σ ∘ z) := by
  refine ⟨hz.1, ?_⟩
  rw [Set.range_comp, ← Ideal.map_span]
  change (Ideal.map σ.toRingHom _).radical = _
  rw [← Ideal.map_radical_of_surjective σ.surjective
    (by
      intro a ha
      have : a = 0 := σ.injective (by simpa using ha)
      simpa only [this] using (Ideal.span (Set.range z)).zero_mem), hz.2]
  exact IsLocalRing.map_ringEquiv_maximalIdeal σ

/-- パラメータ系の各成分を正の冪にしてもパラメータ系である。
生成イデアルの根基が変わらないことを直接示す。 -/
theorem IsSystemOfParameters.pow [IsLocalRing D] {h : ℕ} {z : Fin h → D}
    (hz : IsSystemOfParameters D z) (v : ℕ) (hv : 0 < v) :
    IsSystemOfParameters D (fun i ↦ z i ^ v) := by
  refine ⟨hz.1, le_antisymm ?_ ?_⟩
  · rw [← hz.2]
    apply Ideal.radical_mono
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) v hv
  · rw [← hz.2]
    have hle : Ideal.span (Set.range z) ≤
        (Ideal.span (Set.range fun i ↦ z i ^ v)).radical := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_radical_iff.mpr ⟨v, Ideal.subset_span (Set.mem_range_self i)⟩
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hle

end SerrePositivity
