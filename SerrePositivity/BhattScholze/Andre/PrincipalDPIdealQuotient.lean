module

public import SerrePositivity.BhattScholze.Andre.PrincipalDPCoefficientQuotient

/-!
# André E1・E2：主分冪表示と任意の係数イデアル商

## 概要

主分冪表示を係数イデアルで割ることと、係数商上で同じ表示を作ることは可換。
BS Rem 7.15(1)（著者版 p.62）の二元係数商での pd 包比較に用いる。

## 方針

自由分冪基底の座標で係数変更射の核を求め、一次関係との二重商を交換する。

## 規約

係数イデアルの主性・正則性・標数を仮定しない。実分冪構造の移送は別工程。

## 使われ方

raw p 除算の二元剰余を、同じ係数商上の標準 pd 表示へ同定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A]
section Free
variable (I : Ideal A)
local notation "DA" => DividedPowerAlgebra A A
local notation "R" => A ⧸ I
local notation "bar" => Ideal.Quotient.mk I
local notation "J" => I.map (algebraMap A DA)

/-- 概要：係数商へ送る自由分冪環射の核は係数イデアル I の像イデアル。
方針：標準基底座標の I への所属から各基底項を像イデアル内に足し戻す。
規約：I は任意のイデアル。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実台環の係数商比較。 -/
theorem rankOneDPIdealQuotient_ker :
    RingHom.ker (rankOneDPRingMap bar) = J := by
  classical
  apply le_antisymm
  · intro t ht
    have hzero : rankOneDPRingMap bar t = 0 := ht
    rw [← (rankOneDPAnyBasis A).linearCombination_repr t,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (J).sum_mem
    intro n _
    have hc : bar ((rankOneDPAnyBasis A).repr t n) = 0 := by
      rw [← rankOneDPRingMap_repr, hzero]
      simp
    rw [Algebra.smul_def]
    exact (J).mul_mem_right _ (Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hc))
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change rankOneDPRingMap bar (algebraMap A DA b) = 0
    rw [rankOneDPRingMap_coeff, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

/-- 概要：自由分冪代数の係数イデアル商は係数商上の自由分冪代数と環同型。
方針：核の同定と全射性に第一同型定理を適用する。
規約：標準係数射と全次数の標準分冪を保つ同型。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係商の係数変更。 -/
def rankOneDPIdealQuotientEquiv :
    (DA ⧸ J) ≃+* DividedPowerAlgebra R R :=
  (Ideal.quotEquivOfEq (rankOneDPIdealQuotient_ker I).symm).trans
    ((rankOneDPRingMap bar).quotientKerEquivOfSurjective
      (rankOneDPRingMap_surjective bar Ideal.Quotient.mk_surjective))

/-- 概要：係数商同型は代表元を元の係数変更射で送る。
方針：第一同型定理の代表元公式を使う。
規約：自由分冪代数の全ての元を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の関係元の照合。 -/
theorem rankOneDPIdealQuotientEquiv_mk (t : DA) :
    rankOneDPIdealQuotientEquiv I (Ideal.Quotient.mk _ t) =
      rankOneDPRingMap bar t := rfl

end Free
section Principal
variable (K : Ideal A) (y : A)
local notation "DA" => DividedPowerAlgebra A A
local notation "R" => A ⧸ K
local notation "bar" => Ideal.Quotient.mk K
local notation "C" => K.map (algebraMap A DA)
local notation "I" => principalDPRelationIdeal y

/-- 概要：自由分冪代数の係数商同型は一次関係イデアルの像を保つ。
方針：両イデアルの一つの生成元を係数と標準分冪の公式で照合する。
規約：係数商の元 y mod K を新しい入力とする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の台環比較。 -/
theorem principalDPRelationIdeal_map_idealQuotient :
    principalDPRelationIdeal (bar y) =
      ((I).map (Ideal.Quotient.mk C)).map (rankOneDPIdealQuotientEquiv K).toRingHom := by
  rw [Ideal.map_map, principalDPRelationIdeal, principalDPRelationIdeal,
    Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  change DividedPowerAlgebra.dp R 1 (1 : R) - algebraMap R _ (bar y) =
    rankOneDPIdealQuotientEquiv K
      (Ideal.Quotient.mk C (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A DA y))
  rw [rankOneDPIdealQuotientEquiv_mk, map_sub,
    rankOneDPRingMap_dp, rankOneDPRingMap_coeff]

/-- 概要：一次関係分冪表示の係数イデアル商は係数商上の同じ表示と環同型。
方針：二重商の順序交換と自由分冪の係数商同型を合成する。
規約：実際の二つのイデアル商を用いる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
def principalDPIdealQuotientEquiv :
    ((PrincipalDPPresentation A y) ⧸
      K.map (algebraMap A (PrincipalDPPresentation A y))) ≃+*
        PrincipalDPPresentation R (bar y) :=
  ((Ideal.quotEquivOfEq (show
      K.map (algebraMap A (PrincipalDPPresentation A y)) =
        (C).map (Ideal.Quotient.mk I) by
      rw [Ideal.map_map]
      rfl)).trans (DoubleQuot.quotQuotEquivComm I C)).trans
    (Ideal.quotientEquiv _ _ (rankOneDPIdealQuotientEquiv K)
      (principalDPRelationIdeal_map_idealQuotient K y))

/-- 概要：二重商の比較同型は自由分冪代数の代表元を係数変更射で送る。
方針：二重商順序交換と商同型の代表元公式を使う。
規約：自由分冪代数の全ての元で述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数と全分冪生成元の照合。 -/
theorem principalDPIdealQuotientEquiv_mk_mk (t : DA) :
    principalDPIdealQuotientEquiv K y
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I t)) =
        Ideal.Quotient.mk (principalDPRelationIdeal (bar y)) (rankOneDPRingMap bar t) := by
  simp only [principalDPIdealQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  rw [show Ideal.Quotient.mk _ (Ideal.Quotient.mk I t) =
    DoubleQuot.quotQuotMk I C t from rfl,
    DoubleQuot.quotQuotEquivComm_quotQuotMk]
  change Ideal.quotientEquiv _ _ _ _
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk C t)) = _
  rw [Ideal.quotientEquiv_mk, rankOneDPIdealQuotientEquiv_mk]

/-- 概要：一次関係表示の係数商比較は標準係数を保つ。
方針：自由分冪代表元公式と係数変更射の公式を使う。
規約：元の係数環 A の全ての元を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の入力元の係数変更。 -/
theorem principalDPIdealQuotientEquiv_coeff (b : A) :
    principalDPIdealQuotientEquiv K y
      (Ideal.Quotient.mk _ (algebraMap A (PrincipalDPPresentation A y) b)) =
        algebraMap R (PrincipalDPPresentation R (bar y)) (bar b) := by
  change principalDPIdealQuotientEquiv K y
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (algebraMap A DA b))) = _
  rw [principalDPIdealQuotientEquiv_mk_mk, rankOneDPRingMap_coeff]
  rfl

/-- 概要：一次関係表示の係数商比較は標準分冪生成元の次数を保つ。
方針：自由分冪代表元公式と標準分冪の係数変更を使う。
規約：全ての次数 n を含める。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
theorem principalDPIdealQuotientEquiv_generator (n : ℕ) :
    principalDPIdealQuotientEquiv K y
      (Ideal.Quotient.mk _ (principalDPGenerator y n)) = principalDPGenerator (bar y) n := by
  change principalDPIdealQuotientEquiv K y
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (DividedPowerAlgebra.dp A n (1 : A)))) = _
  rw [principalDPIdealQuotientEquiv_mk_mk, rankOneDPRingMap_dp]
  rfl

end Principal
end SerrePositivity.BhattScholze.Andre
