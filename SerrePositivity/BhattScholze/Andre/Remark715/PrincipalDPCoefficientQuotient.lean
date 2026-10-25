module

public import SerrePositivity.BhattScholze.Andre.Remark715.RankOneDPCoefficientQuotient

/-!
# André E1・E2：一次関係分冪表示と係数主イデアル商の交換

## 概要

一次関係 γ₁=y を持つ分冪表示環を係数元 c で割ることと、A/(c) 上で同じ表示を
作ることは可換。BS Rem 7.15(1)（著者版 p.62）の実 pd 包の係数変更の台環比較。

## 方針

自由分冪代数内で係数主イデアルと一次関係イデアルによる二重商の順序を交換する。
自由分冪代数の係数商同型で一次関係の像を計算し、さらに商同型へ降ろす。

## 規約

標数、正則性、モニック性を仮定しない通常環同型。実分冪構造の移送は別工程。

## 使われ方

ϖ の持上げで還元した実 pd 包を原典の係数環上の標準表示へ移す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (c y : A)
local notation "DA" => DividedPowerAlgebra A A
local notation "R" => A ⧸ Ideal.span {(c : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(c : A)})
local notation "C" => Ideal.span {algebraMap A DA c}
local notation "I" => principalDPRelationIdeal y

/-- 概要：自由分冪代数の係数商同型は一次関係イデアルの像を保つ。
方針：両イデアルの一つの生成元を係数と標準分冪の公式で照合する。
規約：係数商の元 y mod c を新しい入力とする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の台環比較。 -/
theorem principalDPRelationIdeal_map_coefficientQuotient :
    principalDPRelationIdeal (bar y) =
      ((I).map (Ideal.Quotient.mk C)).map (rankOneDPCoefficientQuotientEquiv c).toRingHom := by
  rw [Ideal.map_map, principalDPRelationIdeal, principalDPRelationIdeal,
    Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  change DividedPowerAlgebra.dp R 1 (1 : R) - algebraMap R _ (bar y) =
    rankOneDPCoefficientQuotientEquiv c
      (Ideal.Quotient.mk C (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A DA y))
  rw [rankOneDPCoefficientQuotientEquiv_mk, map_sub,
    rankOneDPRingMap_dp, rankOneDPRingMap_coeff]

/-- 概要：一次関係分冪表示の係数主イデアル商は係数商上の同じ表示と環同型。
方針：二重商の順序交換と自由分冪の係数商同型を合成する。
規約：実際の二つの主イデアル商を用いる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
def principalDPCoefficientQuotientEquiv :
    ((PrincipalDPPresentation A y) ⧸
      Ideal.span {algebraMap A (PrincipalDPPresentation A y) c}) ≃+*
        PrincipalDPPresentation R (bar y) :=
  ((Ideal.quotEquivOfEq (show
      Ideal.span {algebraMap A (PrincipalDPPresentation A y) c} =
        (C).map (Ideal.Quotient.mk I) by
      rw [Ideal.map_span, Set.image_singleton]
      rfl)).trans (DoubleQuot.quotQuotEquivComm I C)).trans
    (Ideal.quotientEquiv _ _ (rankOneDPCoefficientQuotientEquiv c)
      (principalDPRelationIdeal_map_coefficientQuotient c y))

/-- 概要：二重商の比較同型は自由分冪代数の代表元を係数変更射で送る。
方針：二重商順序交換と商同型の代表元公式を使う。
規約：自由分冪代数の全ての元で述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数と全分冪生成元の照合。 -/
theorem principalDPCoefficientQuotientEquiv_mk_mk (t : DA) :
    principalDPCoefficientQuotientEquiv c y
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I t)) =
        Ideal.Quotient.mk (principalDPRelationIdeal (bar y)) (rankOneDPRingMap bar t) := by
  simp only [principalDPCoefficientQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  rw [show Ideal.Quotient.mk _ (Ideal.Quotient.mk I t) =
    DoubleQuot.quotQuotMk I C t from rfl,
    DoubleQuot.quotQuotEquivComm_quotQuotMk]
  change Ideal.quotientEquiv _ _ _ _
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk C t)) = _
  rw [Ideal.quotientEquiv_mk, rankOneDPCoefficientQuotientEquiv_mk]

/-- 概要：一次関係表示の係数商比較は標準係数を保つ。
方針：自由分冪代表元公式と係数変更射の公式を使う。
規約：元の係数環 A の全ての元を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の入力元の係数変更。 -/
theorem principalDPCoefficientQuotientEquiv_coeff (b : A) :
    principalDPCoefficientQuotientEquiv c y
      (Ideal.Quotient.mk _ (algebraMap A (PrincipalDPPresentation A y) b)) =
        algebraMap R (PrincipalDPPresentation R (bar y)) (bar b) := by
  change principalDPCoefficientQuotientEquiv c y
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (algebraMap A DA b))) = _
  rw [principalDPCoefficientQuotientEquiv_mk_mk, rankOneDPRingMap_coeff]
  rfl

/-- 概要：一次関係表示の係数商比較は標準分冪生成元の次数を保つ。
方針：自由分冪代表元公式と標準分冪の係数変更を使う。
規約：全ての次数 n を含める。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
theorem principalDPCoefficientQuotientEquiv_generator (n : ℕ) :
    principalDPCoefficientQuotientEquiv c y
      (Ideal.Quotient.mk _ (principalDPGenerator y n)) = principalDPGenerator (bar y) n := by
  change principalDPCoefficientQuotientEquiv c y
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (DividedPowerAlgebra.dp A n (1 : A)))) = _
  rw [principalDPCoefficientQuotientEquiv_mk_mk, rankOneDPRingMap_dp]
  rfl

variable {B : Type v} [CommRing B]

/-- 概要：指定した係数元の商を、入力を保つ係数商同型に沿って標準表示へ移す。
方針：等しい主イデアルの商同型、係数商の交換、表示環同型を合成する。
規約：係数像との等式 hc を明示し、特殊な係数作用の塔にも適用する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根実 pd 包の比較。 -/
def principalDPReducedCoefficientEquiv
    (cD : PrincipalDPPresentation A y) (hc : cD = algebraMap A _ c)
    (e : (A ⧸ Ideal.span {c}) ≃+* B) (zB : B) (hy : e (bar y) = zB) :
    ((PrincipalDPPresentation A y) ⧸ Ideal.span {cD}) ≃+* PrincipalDPPresentation B zB :=
  ((Ideal.quotEquivOfEq (congrArg (fun t => Ideal.span {t}) hc)).trans
    (principalDPCoefficientQuotientEquiv c y)).trans
      (principalDPRingEquivOfEq e (bar y) zB hy)

/-- 概要：係数還元と入力同型の合成は標準分冪生成元を保つ。
方針：三つの商比較の生成元公式を順に適用する。
規約：全次数を含む一般係数の計算として述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的係数環での計算規則。 -/
theorem principalDPReducedCoefficientEquiv_generator
    (cD : PrincipalDPPresentation A y) (hc : cD = algebraMap A _ c)
    (e : (A ⧸ Ideal.span {c}) ≃+* B) (zB : B) (hy : e (bar y) = zB) (n : ℕ) :
    principalDPReducedCoefficientEquiv c y cD hc e zB hy
      (Ideal.Quotient.mk _ (principalDPGenerator y n)) = principalDPGenerator zB n := by
  simp only [principalDPReducedCoefficientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, principalDPCoefficientQuotientEquiv_generator,
    principalDPRingEquivOfEq_generator]

/-- 概要：係数還元と入力同型の合成は標準係数を対応する係数へ送る。
方針：三つの商比較の係数公式を合成する。
規約：元の係数環 A の任意の元で述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的係数作用の比較。 -/
theorem principalDPReducedCoefficientEquiv_coeff
    (cD : PrincipalDPPresentation A y) (hc : cD = algebraMap A _ c)
    (e : (A ⧸ Ideal.span {c}) ≃+* B) (zB : B) (hy : e (bar y) = zB) (b : A) :
    principalDPReducedCoefficientEquiv c y cD hc e zB hy
      (Ideal.Quotient.mk _ (algebraMap A (PrincipalDPPresentation A y) b)) =
        algebraMap B (PrincipalDPPresentation B zB) (e (bar b)) := by
  simp only [principalDPReducedCoefficientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, principalDPCoefficientQuotientEquiv_coeff,
    principalDPRingEquivOfEq_coeff]

end SerrePositivity.BhattScholze.Andre
