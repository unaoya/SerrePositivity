module

public import SerrePositivity.Inputs.CohenNormalization
public import SerrePositivity.CommutativeAlgebra.FiniteParameters
public import SerrePositivity.CommutativeAlgebra.RegularNormality
public import SerrePositivity.CommutativeAlgebra.SeparableBaseChange
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
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

標数 `p` では `Inputs.cohen_gabber_normalization`、混標数では
`Inputs.cohen_normalization_mixedCharacteristic` の証明済みの実構成を適用する。
等標数の引用の範囲と出典は `Inputs/CohenNormalization.lean` に明記した。
標数の二分、有限拡大による次元の一致と
パラメータ系の移送、分数体の分離性から最小多項式の条件への移送をここで証明する。
混標数の分離性は標数零から従う。正規性の導出は証明済みの正則パラメータから従う。

## 主張の形と、下流で使う部分

結論は `A`（環・正則局所環・完備・`D` 代数の構造）、単射性、有限性、生成的分離性、剰余体の一致、
次元、正則パラメータ系 `t` と、それが `D` のパラメータ系であることを連言で返す。

`A` の具体形（`k[[t]]` または `W(k)[[t₂, …]]` との環同型で `t_i ↦ X_i`）も結論に入れた。ただし
**下流（Theorem 2.5 の主張、Corollary 2.6、Lemma 3.4、3.5、§5）で使うのは抽象的な性質だけ**で、
具体形は Theorem 2.5 の証明（標数 `p` では `Λ = A_perf`、混標数では CLMST の設定 `A = W(k)[[x]]`）
でしか要らない。利用側はこの連言から必要な性質だけを取り出して使う。

- 生成的分離は、各元の最小多項式の係数を `FractionRing A` に移した後の分離性で書く。
  正規な整域 `A` では `Frac D / Frac A` の分離性と同じ条件になる。
  環上の `Algebra.IsSeparable A D` はこれより強いため、使用しない。
- 混標数の具体形は、`t ⟨0, _⟩ = p` と、残りの添字 `{i // i ≠ 0}` 上の冪級数環 `W(k)[[X]]` への
  同型で書く。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

namespace Section2

/-- **Lemma 2.2**（正則な正規化基底）。二つの正規化の引用から論文の条件を導く。 -/
theorem lemma_2_2 (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      (∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧ ringKrullDim A = h ∧
      ∃ t : Fin h → A, Ideal.span (Set.range t) = maximalIdeal A ∧
        IsSystemOfParameters D (algebraMap A D ∘ t) ∧
        -- 具体形（下流では使わない）
        ((CharP D p ∧ ∃ e : A ≃+* MvPowerSeries (Fin h) (ResidueField D),
            ∀ i, e (t i) = MvPowerSeries.X i) ∨
          (CharZero D ∧ t ⟨0, hpos⟩ = (p : A) ∧
            ∃ e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)),
              ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)) := by
  rcases CharP.exists' D with hzero | ⟨q, hq, hchar⟩
  · let := hzero
    obtain ⟨A, aRing, aDomain, aRegular, aComplete, aAlg,
      hinj, hfinite, hres, t, e, ht, hp, he⟩ :=
      Inputs.cohen_normalization_mixedCharacteristic D hdim hpos p
    let := hfinite
    let : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
    let : CharZero A := (algebraMap A D).charZero
    let : Module.IsTorsionFree A D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
    let : Algebra (FractionRing A) (FractionRing D) :=
      FractionRing.liftAlgebra A (FractionRing D)
    let : IsScalarTower A (FractionRing A) (FractionRing D) :=
      FractionRing.isScalarTower_liftAlgebra A (FractionRing D)
    have hA : ringKrullDim A = h :=
      (ringKrullDim_eq_of_integral_of_injective A D hinj).symm.trans hdim
    have hsop : IsSystemOfParameters A t :=
      ⟨hA, by rw [ht]; exact (maximalIdeal.isMaximal A).isPrime.radical⟩
    refine ⟨A, aRing, aRegular, aComplete, aAlg, hinj, hfinite, ?_, hres, hA,
      t, ht, hsop.map_finite D hinj, Or.inr ⟨hzero, hp, e, he⟩⟩
    exact (separable_minpoly_iff_fractionRing A D (FractionRing A) (FractionRing D)).mpr
      inferInstance
  · let := hq
    let := hchar
    have hqp : p = q := (Nat.dvd_prime hq.out).mp
      (CharP.dvd_of_ringHom (residue D) q p) |>.resolve_left (Fact.out : p.Prime).ne_one
    subst q
    obtain ⟨A, aRing, aDomain, aRegular, aComplete, aAlg,
      hinj, hfinite, hres, ⟨fracAlg, fracTower, hsep⟩, t, e, ht, he⟩ :=
      Inputs.cohen_gabber_normalization D hdim p
    let := hfinite
    let : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
    have hA : ringKrullDim A = h :=
      (ringKrullDim_eq_of_integral_of_injective A D hinj).symm.trans hdim
    have hsop : IsSystemOfParameters A t :=
      ⟨hA, by rw [ht]; exact (maximalIdeal.isMaximal A).isPrime.radical⟩
    refine ⟨A, aRing, aRegular, aComplete, aAlg, hinj, hfinite, ?_, hres, hA,
      t, ht, hsop.map_finite D hinj, Or.inl ⟨hchar, e, he⟩⟩
    exact (separable_minpoly_iff_fractionRing A D (FractionRing A) (FractionRing D)).mpr hsep

end Section2

end SerrePositivity
