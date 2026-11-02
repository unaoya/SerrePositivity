module

public import SerrePositivity.CommutativeAlgebra.CohenGabber.Normalization
public import SerrePositivity.CommutativeAlgebra.Witt.Normalization
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Normality
public import SerrePositivity.FieldTheory.SeparableBaseChange
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic

/-! # 正則な正規化基底（論文 Lemma 2.2）

## 概要

次元 `h > 0` の完備 Noether 局所整域 `(D, 𝔡, k)`（`k` は標数 `p > 0` の完全体）に対し、有限で生成的分離な包含 `A ⊆ D` で剰余体に恒等写像を誘導するものがある。`char D = p` なら `A = k[[t₁, …, t_h]]`、`char D = 0` なら `A = W(k)[[t₂, …, t_h]]`（`t₁ = p`）で、`t` は `D` のパラメータ系かつ `A` の正則パラメータ系。

## 方針

標数 `p` では `exists_cohen_gabber_normalization`（CommutativeAlgebra/CohenGabber）、混標数では `exists_cohen_normalization_mixedCharacteristic`（CommutativeAlgebra/Witt）を適用し、標数の二分、有限拡大による次元の一致とパラメータ系の移送、分数体の分離性から最小多項式の条件への移送をここで示す。

## 規約

結論は `A` の構造・単射性・有限性・生成的分離性・剰余体の一致・次元・正則パラメータ系を連言で返す。`A` の具体形（`k[[t]]` または `W(k)[[t₂, …]]` との同型）も結論に入れるが、下流で使うのは抽象的な性質だけで、具体形は Theorem 2.5 の証明でしか要らない。生成的分離は各元の最小多項式を `FractionRing A` に移した後の分離性で書く（`Algebra.IsSeparable A D` はこれより強いので使わない）。

## 使われ方

Paper/Section5/Setup（`GaloisNormalization`）、Theorem 2.5。
-/

@[expose] public noncomputable section

universe u

section Lemma2_2Part

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
      exists_cohen_normalization_mixedCharacteristic D hdim hpos p
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
      exists_cohen_gabber_normalization D hdim p
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

end Lemma2_2Part
