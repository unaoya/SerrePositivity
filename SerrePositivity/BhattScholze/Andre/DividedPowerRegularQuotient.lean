module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# André E1・E2：正次数商で正則な元による実分冪構造の降下

## 概要

環 D の分冪イデアル J に対し、D/J で正則な元 a による商へ実分冪構造が降りる。
BS Rem 7.15(1)（著者版 p.62）の係数 R/ϖ への比較のための一般補題。

## 方針

ab が J に入れば商での a の正則性により b も J に入る。
γₙ(ab)=aⁿγₙ(b) から (a) と J の交わりの分冪安定性を得て、商 API を適用する。

## 規約

a の環 D 自身での正則性は要求しない。分冪イデアルによる商での正則性を明示する。

## 使われ方

正次数商の係数環上の自由性から係数元の正則性を供給し、実分冪構造を係数商へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {D : Type u} [CommRing D] {J : Ideal D} (H : DividedPowers J) (a : D)
variable (ha : IsSMulRegular (D ⧸ J) (Ideal.Quotient.mk J a))
include ha

/-- 概要：D/J で正則な a に対し (a) と J の交わりは分冪で保たれる。
方針：ab が J に属すれば b も属し、正次数分冪は a の倍数になる。
規約：全ての正次数を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数元による分冪降下の入力。 -/
theorem dividedPower_regular_span_inf_isSubDPIdeal :
    H.IsSubDPIdeal (Ideal.span {a} ⊓ J) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn x hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx.1
  have hb : Ideal.Quotient.mk J b = 0 := by
    apply ha
    change Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = Ideal.Quotient.mk J a * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx.2
  have hbJ : b ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hb
  refine ⟨?_, H.dpow_mem hn hx.2⟩
  rw [H.dpow_mul hbJ]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left (dvd_pow_self a hn) _)

/-- 概要：D/J で正則な元 a による商の像イデアルに実分冪構造を与える。
方針：(a) と J の交わりの分冪安定性を商構成へ渡す。
規約：対象は J の実商射による像である。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商上の実 pd 構造。 -/
def dividedPowersQuotientOfRegular :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {a}))) :=
  DividedPowers.Quotient.dividedPowers H (dividedPower_regular_span_inf_isSubDPIdeal H a ha)

/-- 概要：降下した分冪作用は元の分冪値の商像に一致する。
方針：実商の分冪作用の標準評価公式を使う。
規約：元を元の分冪イデアル J 内に取る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の生成元と普遍性の比較。 -/
theorem dividedPowersQuotientOfRegular_apply (n : ℕ) {x : D} (hx : x ∈ J) :
    (dividedPowersQuotientOfRegular H a ha).dpow n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (H.dpow n x) :=
  DividedPowers.Quotient.dpow_apply H (dividedPower_regular_span_inf_isSubDPIdeal H a ha) hx

/-- 概要：正則係数元による標準商射は分冪射。
方針：商構成の分冪射の互換性を使う。
規約：元のイデアル J とその実像を比較する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
theorem dividedPowersQuotientOfRegular_isDPMorphism :
    H.IsDPMorphism (dividedPowersQuotientOfRegular H a ha) (Ideal.Quotient.mk (Ideal.span {a})) :=
  DividedPowers.Quotient.isDPMorphism H (dividedPower_regular_span_inf_isSubDPIdeal H a ha)

end SerrePositivity.BhattScholze.Andre
