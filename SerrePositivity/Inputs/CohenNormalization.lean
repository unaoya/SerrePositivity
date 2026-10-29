module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import SerrePositivity.CommutativeAlgebra.Witt.Normalization
public import SerrePositivity.CommutativeAlgebra.CohenGabber.Normalization

/-! # 証明済みのCohen–Gabberと混標数Cohen正規化

標準座標を持つ完備正則局所部分環を構成する。
等標数ではGabberの微分経路から分数体拡大の分離性も証明済み。
混標数の正規化はWitt係数写像・パラメータ・実際の冪級数評価から証明済み。
混標数の分離性は利用側で標数零から導く。
基底の次元と、座標の像がパラメータ系になることも利用側で証明する。

正則性・完備性・標準座標による極大イデアルの生成は、形式冪級数環の標準的な
性質を既存の冪級数の構造定理から供給する。
混標数側の公開型は互換入口として保持し、証明済みの構成を適用する。
-/

public section

universe u

namespace SerrePositivity.Inputs

open IsLocalRing

/-- **証明済み：Cohen–Gabber 正規化（整域の場合、標準座標付き）。**
Kurano–Shimomoto, *An elementary proof of Cohen–Gabber theorem in the equal
characteristic p > 0 case*, Theorem 1.1。
https://arxiv.org/abs/1510.03573

原文の係数体とパラメータで作る部分環を `A` とし、標準座標を `t` とする。
形式冪級数環の正則性・完備性には Stacks Project, Remark 10.160.9 を併用する。
https://stacks.math.columbia.edu/tag/0323
分離性は環上ではなく、両立する分数体の代数構造について述べる。
Gabberの微分経路で係数体を変更し、微分基底となるパラメータを選び、
同じ有限単射の相対微分の生成的消滅から分離性を証明する。 -/
theorem cohen_gabber_normalization
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧
      (∃ (_ : Algebra (FractionRing A) (FractionRing D))
        (_ : IsScalarTower A (FractionRing A) (FractionRing D)),
        Algebra.IsSeparable (FractionRing A) (FractionRing D)) ∧
      ∃ (t : Fin h → A) (e : A ≃+* MvPowerSeries (Fin h) (ResidueField D)),
        Ideal.span (Set.range t) = maximalIdeal A ∧
        ∀ i, e (t i) = MvPowerSeries.X i := by
  exact SerrePositivity.exists_cohen_gabber_normalization D hdim p

/-- **証明済み：Cohen 正規化（混標数、完全剰余体の場合）。**
Stacks Project, Lemma 10.160.11 の混標数分岐と Remark 10.160.9。
https://stacks.math.columbia.edu/tag/0323
完全剰余体の場合の Cohen 環を `W(k)` と同定し、`p` と残りの形式変数を座標とする形。
Witt係数写像と指定剰余体の両立、pを含むパラメータ、冪級数基底の構造、
評価の有限性、次元一致による単射性を実構成して証明した。
生成的分離性・`D` のパラメータ系への利用側の移送は別に証明する。 -/
theorem cohen_normalization_mixedCharacteristic
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [CharZero D] [IsAdicComplete (maximalIdeal D) D]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧
      ∃ (t : Fin h → A)
        (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D))),
        Ideal.span (Set.range t) = maximalIdeal A ∧ t ⟨0, hpos⟩ = (p : A) ∧
        ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩ := by
  exact SerrePositivity.exists_cohen_normalization_mixedCharacteristic D hdim hpos p

end SerrePositivity.Inputs
