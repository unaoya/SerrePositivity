module

public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic

/-!
# Lemma 2.2（正則な正規化基底）

## 概要

論文 Lemma 2.2：`(D, 𝔡, k)` を次元 `h > 0` の完備 Noether 局所整域、`k` を標数 `p > 0` の完全体
とする。有限で生成的分離な包含 `A ⊆ D` で剰余体に恒等写像を誘導し、

- `char D = p` なら `A = k[[t₁, …, t_h]]`、
- `char D = 0` なら `A = W(k)[[t₂, …, t_h]]`（`t₁ = p` とおく）

となるものがある。どちらの場合も `t₁, …, t_h` は `D` のパラメータ系かつ `A` の正則パラメータ系。

証明は標数 `p` では Cohen–Gabber の正規化定理（Kurano–Shimomoto [17, Thm 1.1]）、混標数では
Cohen の構造定理（係数環 `W(k) ⊆ D`）による。どちらも深い定理なので主張だけ置く（`sorry`）。

## 主張の形と、下流で使う部分

結論は `A`（環・正則局所環・完備・`D` 代数の構造）、単射性、有限性、生成的分離性、剰余体の一致、
次元、正則パラメータ系 `t` と、それが `D` のパラメータ系であることを連言で返す。

`A` の具体形（`k[[t]]` または `W(k)[[t₂, …]]` との環同型で `t_i ↦ X_i`）も結論に入れた。ただし
**下流（Theorem 2.5 の主張、Corollary 2.6、Lemma 3.4、3.5、§5）で使うのは抽象的な性質だけ**で、
具体形は Theorem 2.5 の証明（標数 `p` では `Λ = A_perf`、混標数では CLMST の設定 `A = W(k)[[x]]`）
でしか要らない。利用側はこの連言から必要な性質だけを取り出して使う。

- 生成的分離は `Algebra.IsSeparable A D`（`D` の各元の `A` 上の最小多項式が分離的）で書く。
  `A` は正則なので正規で、`Frac D / Frac A` の分離性と同じ。
- 混標数の具体形は、`t ⟨0, _⟩ = p` と、残りの添字 `{i // i ≠ 0}` 上の冪級数環 `W(k)[[X]]` への
  同型で書く。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

namespace Section2

/-- **Lemma 2.2**（正則な正規化基底、`sorry`：Cohen–Gabber と Cohen の構造定理）。 -/
theorem lemma_2_2 (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧ Algebra.IsSeparable A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧ ringKrullDim A = h ∧
      ∃ t : Fin h → A, Ideal.span (Set.range t) = maximalIdeal A ∧
        IsSystemOfParameters D (algebraMap A D ∘ t) ∧
        -- 具体形（下流では使わない）
        ((CharP D p ∧ ∃ e : A ≃+* MvPowerSeries (Fin h) (ResidueField D),
            ∀ i, e (t i) = MvPowerSeries.X i) ∨
          (CharZero D ∧ t ⟨0, hpos⟩ = (p : A) ∧
            ∃ e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)),
              ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)) := by
  sorry

end Section2

end SerrePositivity
