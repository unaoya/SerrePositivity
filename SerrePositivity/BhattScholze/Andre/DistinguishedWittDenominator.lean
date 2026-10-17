module

public import SerrePositivity.BhattScholze.DeltaPDivisionWittResidueSolution
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# André E1・E2：Witt 方程式の distinguished 分母の正規化

## 概要

標数 p の環 B への係数射 q が d を殺すとき、qW(φ(d)) は p の単元倍。
BS Rem 7.15（著者版 p.62）の raw 剰余と pd 包の比較に使う。

## 方針

W(d) の像の係数を一段ずらした元 v は p v=qW(φ(d)) を満たす。
v の定数係数 q(δd) が単元なので、Witt ベクトルの再帰的逆元を使う。

## 規約

源は p 正則、d は distinguished とし、終域に δ 構造を要求しない。
原典とは異なる具体的 Witt 方程式による分母変換である。

## 使われ方

φ(d) による除算方程式の解を p による除算方程式の解へ可逆に移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B] [CharP B p]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (q : A →+* B) (d : A) (hd : D.IsDistinguished d)

omit [CharP B p] in
include hpA hd in
/-- 概要：d の Witt 除算解の定数係数は単元。
方針：定数係数を q(δd) と計算し distinguished 性を送る。
規約：源の p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の分母の単元倍への正規化。 -/
theorem distinguishedWittDenominator_coeff_zero_isUnit :
    IsUnit ((deltaPDivisionWittResidueSolution D q d).coeff 0) := by
  rw [deltaPDivisionWittResidueSolution_coeff_zero D q d hpA]
  exact hd.map q

/-- 概要：係数をずらした Witt 元をそのまま値に持つ単元。
方針：定数係数の単元性を Witt ベクトルの再帰的逆元へ渡す。
規約：単元の値を具体的な Witt 解のまま保持する。
使われ方：BS Rem 7.15（著者版 p.62）の除算変数の可逆な変換。 -/
def distinguishedWittDenominatorUnit : (WittVector p B)ˣ :=
  WittVector.mkUnit
    (distinguishedWittDenominator_coeff_zero_isUnit D hpA q d hd).unit_spec.symm

/-- 概要：選んだ単元の値は既存の具体的 Witt 除算解。
方針：Witt 単元の定義を使う。
規約：選択に依存しない値の等式。
使われ方：BS Rem 7.15（著者版 p.62）の係数公式との接続。 -/
theorem distinguishedWittDenominatorUnit_val :
    (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) =
      deltaPDivisionWittResidueSolution D q d := rfl

/-- 概要：d を殺す係数射の下で φ(d) の全 Witt 像は p の単元倍。
方針：具体的 Witt 解の除算方程式を使う。
規約：ghost 射の単射性と q(d)=0 を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 分母を p に変換する計算。 -/
theorem distinguishedWittDenominatorUnit_mul
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) :
    (p : WittVector p B) * distinguishedWittDenominatorUnit D hpA q d hd =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift d)) :=
  deltaPDivisionWittResidueSolution_mul D q d hgA hqd

/-- 概要：φ(d) による Witt 除算解と p による除算解は同値。
方針：単元 v による乗法と v⁻¹ による乗法を逆にする。
規約：右辺 z は任意の Witt 元で、終域の δ 構造を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 包比較に供給する Witt 解の変換。 -/
def distinguishedWittDivisionSolutionEquiv
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) (z : WittVector p B) :
    {w : WittVector p B //
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift d)) * w = z} ≃
    {w : WittVector p B // (p : WittVector p B) * w = z} where
  toFun w := ⟨(distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) * w, by
    rw [← mul_assoc, distinguishedWittDenominatorUnit_mul D hpA q d hd hgA hqd]
    exact w.property⟩
  invFun w := ⟨(↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) * w, by
    rw [← distinguishedWittDenominatorUnit_mul D hpA q d hd hgA hqd]
    rw [mul_assoc, ← mul_assoc
      (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B)
      (↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B)
      (w : WittVector p B), Units.mul_inv, one_mul]
    exact w.property⟩
  left_inv w := by
    apply Subtype.ext
    change (↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) *
      ((distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) * w) = w
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv w := by
    apply Subtype.ext
    change (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) *
      ((↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) * w) = w
    rw [← mul_assoc, Units.mul_inv, one_mul]

end SerrePositivity.BhattScholze.Andre
