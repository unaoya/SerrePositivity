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

/-! # 引用：Cohen–Gabber と Cohen による正規化

引用の範囲は、標準座標を持つ完備正則局所部分環の存在である。
等標数では分数体拡大の分離性も Cohen–Gabber の結論として引用する。
混標数では分離性を引用に含めず、標数零から導く。
基底の次元と、座標の像がパラメータ系になることも利用側で証明する。

正則性・完備性・標準座標による極大イデアルの生成は、形式冪級数環の標準的な
性質を合わせた形で引用している。このファイルはそれらの独立した形式化ではない。
-/

public section

universe u

namespace SerrePositivity.Inputs

open IsLocalRing

/-- **引用：Cohen–Gabber 正規化（整域の場合、標準座標付き）。**
Kurano–Shimomoto, *An elementary proof of Cohen–Gabber theorem in the equal
characteristic p > 0 case*, Theorem 1.1。
https://arxiv.org/abs/1510.03573

原文の係数体とパラメータで作る部分環を `A` とし、標準座標を `t` とする。
形式冪級数環の正則性・完備性には Stacks Project, Remark 10.160.9 を併用する。
https://stacks.math.columbia.edu/tag/0323
分離性は環上ではなく、両立する分数体の代数構造について述べる。 -/
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
  sorry

/-- **引用：Cohen 正規化（混標数、完全剰余体の場合）。**
Stacks Project, Lemma 10.160.11 の混標数分岐と Remark 10.160.9。
https://stacks.math.columbia.edu/tag/0323
完全剰余体の場合の Cohen 環を `W(k)` と同定し、`p` と残りの形式変数を座標とする形。
この同定も引用に含む（対象論文 Lemma 2.2 の Cohen 構造定理の適用）。
生成的分離性・次元の一致・`D` のパラメータ系は、この引用には含めない。 -/
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
  sorry

end SerrePositivity.Inputs
