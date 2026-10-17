module

public import SerrePositivity.BhattScholze.Andre.PrincipalDPRingEquiv
public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveUniversal

/-!
# André E1・E2：係数同型による実分冪構造と普遍性の移送

## 概要

一次関係商の正次数イデアルの実分冪構造を、入力を保つ係数環同型に沿って移す。
標準分冪値が生成元に一致する公式と pd 普遍性も移る。
BS Rem 7.15(1)（著者版 p.62）の実係数比較のための一般補題。

## 方針

商同型の全生成元上の公式で正次数イデアルの像を同定し、
既存の環同型による分冪構造の移送を使う。

## 規約

分冪構造の存在と標準値は元の環から供給する。係数環の標数や正則性は仮定しない。

## 使われ方

実 mod p 商上で構成した分冪包を、係数商上の無限根環の同じ入力へ移す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable (e : A ≃+* B) (y : A) (z : B) (hy : e y = z)
local notation "F" => principalDPRingEquivOfEq e y z hy

/-- 概要：入力を保つ係数同型は正次数生成元イデアルを保つ。
方針：各正次数標準生成元の像を計算して生成集合を比較する。
規約：対象イデアルは全正次数生成元の span そのもの。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の移送の入力。 -/
theorem principalDPPositiveIdeal_map_equiv :
    (principalDPPositiveIdeal y).map (F).toRingHom = principalDPPositiveIdeal z := by
  rw [principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun n : ℕ => F (principalDPGenerator y (n + 1))) = _
  simp only [principalDPRingEquivOfEq_generator, principalDPPositiveIdeal]

/-- 概要：入力を保つ係数同型で一次関係商の実分冪構造を移せる。
方針：正次数イデアルの像の同定と環同型による既存の分冪移送を使う。
規約：元の環上の分冪構造を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的な係数表示での実 pd 構造。 -/
def principalDPTransportDividedPowers (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    DividedPowers (principalDPPositiveIdeal z) :=
  DividedPowers.ofRingEquiv (principalDPPositiveIdeal_map_equiv e y z hy) Hs

/-- 概要：移送した構造でも入力元の n 次分冪は n 次標準生成元。
方針：入力係数の比較と環同型による分冪作用の公式を使う。
規約：元の構造についての標準値公式を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の移送後の実 pd 普遍性への入力。 -/
theorem principalDPTransportDividedPowers_base_apply
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A _ y) = principalDPGenerator y n) (n : ℕ) :
    (principalDPTransportDividedPowers e y z hy Hs).dpow n
      (algebraMap B (PrincipalDPPresentation B z) z) = principalDPGenerator z n := by
  have hc : F (algebraMap A _ y) = algebraMap B (PrincipalDPPresentation B z) z := by
    rw [principalDPRingEquivOfEq_coeff, hy]
  rw [← hc, principalDPTransportDividedPowers, DividedPowers.ofRingEquiv_dpow_apply,
    hγ, principalDPRingEquivOfEq_generator]

/-- 概要：移送した実分冪構造を持つ一次関係商から分冪標的への射は一意に存在。
方針：移送後の標準値公式を一次関係商の一般普遍性へ渡す。
規約：標的にねじれ・正則性・δ 構造の条件を置かない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数同型後の実 pd 包。 -/
theorem existsUnique_principalDPTransportMorphism
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A _ y) = principalDPGenerator y n)
    {T : Type w} [CommRing T] [Algebra B T] {I : Ideal T} (Ht : DividedPowers I)
    (hzT : algebraMap B T z ∈ I) :
    ∃! G : PrincipalDPPresentation B z →ₐ[B] T,
      (principalDPTransportDividedPowers e y z hy Hs).IsDPMorphism Ht G.toRingHom :=
  existsUnique_principalDPPositiveMorphism z (principalDPTransportDividedPowers e y z hy Hs)
    (principalDPTransportDividedPowers_base_apply e y z hy Hs hγ) Ht hzT

end SerrePositivity.BhattScholze.Andre
