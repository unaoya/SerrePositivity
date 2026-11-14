module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DividedPowerPrime
public import SerrePositivity.BhattScholze.Delta.DividedPower.Principal.PrincipalDP

/-!
# 一次関係の分冪表示と係数商

## 概要
切断表示、自由一元分冪代数・一次関係の分冪表示と係数主イデアル・係数イデアルの商の交換、正則一元入力の mod p 一次関係商の分冪構造と pd 包の普遍性、正次数分冪イデアルによる商と普遍性、係数同型による移送。
BS 著者版 Lemma 2.38 と Remark 7.15 の一元分冪包の計算に使う、一次関係と係数商を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/DeltaDivisionWitt`、`PowerRootEnvelope/PowerRootInput`、`PowerRootEnvelope/Varpi`、`PowerRootEnvelope/VarpiPD`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`。
-/

universe u v w

/-! ## 自由一元分冪代数の係数主イデアル商

## 概要

自由一元分冪代数を係数元 c で割ると、A/(c) 上の自由一元分冪代数と環同型。
BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪表示の係数変更。

## 方針

任意係数上の標準分冪基底で係数変更射の全射性と核を計算し、第一同型定理を使う。

## 規約

係数環の標数・非零性・c の正則性を要求しない。環同型を構成する段階である。

## 使われ方

一次関係 γ₁=y をさらに商にして、実 pd 包自体の係数変更を比較する。
-/

@[expose] public noncomputable section RankOneDPCoefficientQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 概要：自由分冪の係数変更は標準基底座標を係数環射で送る。
方針：両座標射を係数線形写像として束ね、標準基底上で比較する。
規約：任意の係数環射を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商射の核の計算。 -/
theorem rankOneDPRingMap_repr (φ : A →+* B) (t : DividedPowerAlgebra A A) (n : ℕ) :
    (rankOneDPAnyBasis B).repr (rankOneDPRingMap φ t) n =
      φ ((rankOneDPAnyBasis A).repr t n) := by
  classical
  let := φ.toAlgebra
  let F : DividedPowerAlgebra A A →ₐ[A] DividedPowerAlgebra B B :=
    { rankOneDPRingMap φ with commutes' := rankOneDPRingMap_coeff φ }
  let L := ((rankOneDPAnyBasis B).coord n).restrictScalars A
  have he : L.comp F.toLinearMap =
      (Algebra.linearMap A B).comp ((rankOneDPAnyBasis A).coord n) := by
    apply (rankOneDPAnyBasis A).ext
    intro i
    simp only [LinearMap.comp_apply, L, LinearMap.restrictScalars_apply,
      Module.Basis.coord_apply, AlgHom.toLinearMap_apply]
    change (rankOneDPAnyBasis B).repr
      (rankOneDPRingMap φ (rankOneDPAnyBasis A i)) n = _
    rw [rankOneDPAnyBasis_apply, rankOneDPRingMap_dp, ← rankOneDPAnyBasis_apply B i]
    rw [← rankOneDPAnyBasis_apply A i]
    simp [Module.Basis.repr_self, Finsupp.single_apply, Algebra.linearMap_apply]
  exact congrArg (fun l : DividedPowerAlgebra A A →ₗ[A] B => l t) he

/-- 概要：全射な係数環射は自由分冪代数の全射を誘導する。
方針：標準基底展開の各係数を持ち上げ、像部分環で有限和を取る。
規約：係数環の非零性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更後の環同型。 -/
theorem rankOneDPRingMap_surjective (φ : A →+* B) (hφ : Function.Surjective φ) :
    Function.Surjective (rankOneDPRingMap φ) := by
  classical
  intro t
  change t ∈ (rankOneDPRingMap φ).range
  rw [← (rankOneDPAnyBasis B).linearCombination_repr t,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply (rankOneDPRingMap φ).range.sum_mem
  intro n _
  obtain ⟨b, hb⟩ := hφ ((rankOneDPAnyBasis B).repr t n)
  refine ⟨algebraMap A _ b * DividedPowerAlgebra.dp A n (1 : A), ?_⟩
  rw [map_mul, rankOneDPRingMap_coeff, rankOneDPRingMap_dp, hb,
    Algebra.smul_def, rankOneDPAnyBasis_apply]

variable (c : A)
local notation "DA" => DividedPowerAlgebra A A
local notation "R" => A ⧸ Ideal.span {(c : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(c : A)})

/-- 概要：係数商へ送る自由分冪環射の核は係数元 c の主イデアル。
方針：標準基底座標の c 可除性から各基底項を主イデアル内に足し戻す。
規約：c が零因子でもよい。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実台環の係数商比較。 -/
theorem rankOneDPCoefficientQuotient_ker :
    RingHom.ker (rankOneDPRingMap bar) = Ideal.span {algebraMap A DA c} := by
  classical
  apply le_antisymm
  · intro t ht
    have hzero : rankOneDPRingMap bar t = 0 := ht
    rw [← (rankOneDPAnyBasis A).linearCombination_repr t,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (Ideal.span {algebraMap A DA c}).sum_mem
    intro n _
    have hc : bar ((rankOneDPAnyBasis A).repr t n) = 0 := by
      rw [← rankOneDPRingMap_repr, hzero]
      simp
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    rw [hb, Algebra.smul_def, map_mul, mul_assoc]
    exact (Ideal.span {algebraMap A DA c}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t = algebraMap A DA c := Set.mem_singleton_iff.mp ht
    subst t
    change rankOneDPRingMap bar (algebraMap A DA c) = 0
    rw [rankOneDPRingMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), map_zero]

/-- 概要：自由分冪代数の係数主イデアル商は係数商上の自由分冪代数と環同型。
方針：核の同定と全射性に第一同型定理を適用する。
規約：標準係数射と全次数の標準分冪を保つ同型。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係商の係数変更。 -/
def rankOneDPCoefficientQuotientEquiv :
    (DA ⧸ Ideal.span {algebraMap A DA c}) ≃+* DividedPowerAlgebra R R :=
  (Ideal.quotEquivOfEq (rankOneDPCoefficientQuotient_ker c).symm).trans
    ((rankOneDPRingMap bar).quotientKerEquivOfSurjective
      (rankOneDPRingMap_surjective bar Ideal.Quotient.mk_surjective))

/-- 概要：係数商同型は代表元を元の係数変更射で送る。
方針：第一同型定理の代表元公式を使う。
規約：自由分冪代数の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の関係元の照合。 -/
theorem rankOneDPCoefficientQuotientEquiv_mk (t : DA) :
    rankOneDPCoefficientQuotientEquiv c (Ideal.Quotient.mk _ t) =
      rankOneDPRingMap bar t := rfl

end SerrePositivity.BhattScholze.Andre

end RankOneDPCoefficientQuotient

/-! ## 一次関係分冪表示と係数主イデアル商の交換

## 概要

一次関係 γ₁=y を持つ分冪表示環を係数元 c で割ることと、A/(c) 上で同じ表示を
作ることは可換。BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の係数変更の台環比較。

## 方針

自由分冪代数内で係数主イデアルと一次関係イデアルによる二重商の順序を交換する。
自由分冪代数の係数商同型で一次関係の像を計算し、さらに商同型へ降ろす。

## 規約

標数、正則性、モニック性を仮定しない通常環同型。実分冪構造の移送は別工程。

## 使われ方

ϖ の持上げで還元した実 pd 包を原典の係数環上の標準表示へ移す。
-/

@[expose] public noncomputable section PrincipalDPCoefficientQuotient

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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の台環比較。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数と全分冪生成元の照合。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の入力元の係数変更。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根実 pd 包の比較。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的係数環での計算規則。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的係数作用の比較。 -/
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

end PrincipalDPCoefficientQuotient

/-! ## 主分冪表示と任意の係数イデアル商

## 概要

主分冪表示を係数イデアルで割ることと、係数商上で同じ表示を作ることは可換。
BS 著者版 Remark 7.15(1)（著者版 p.62）の二元係数商での pd 包比較に用いる。

## 方針

自由分冪基底の座標で係数変更射の核を求め、一次関係との二重商を交換する。

## 規約

係数イデアルの主性・正則性・標数を仮定しない。実分冪構造の移送は別工程。

## 使われ方

raw p 除算の二元剰余を、同じ係数商上の標準 pd 表示へ同定する。
-/

@[expose] public noncomputable section PrincipalDPIdealQuotient

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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実台環の係数商比較。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係商の係数変更。 -/
def rankOneDPIdealQuotientEquiv :
    (DA ⧸ J) ≃+* DividedPowerAlgebra R R :=
  (Ideal.quotEquivOfEq (rankOneDPIdealQuotient_ker I).symm).trans
    ((rankOneDPRingMap bar).quotientKerEquivOfSurjective
      (rankOneDPRingMap_surjective bar Ideal.Quotient.mk_surjective))

/-- 概要：係数商同型は代表元を元の係数変更射で送る。
方針：第一同型定理の代表元公式を使う。
規約：自由分冪代数の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の関係元の照合。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の台環比較。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数と全分冪生成元の照合。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の入力元の係数変更。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
theorem principalDPIdealQuotientEquiv_generator (n : ℕ) :
    principalDPIdealQuotientEquiv K y
      (Ideal.Quotient.mk _ (principalDPGenerator y n)) = principalDPGenerator (bar y) n := by
  change principalDPIdealQuotientEquiv K y
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (DividedPowerAlgebra.dp A n (1 : A)))) = _
  rw [principalDPIdealQuotientEquiv_mk_mk, rankOneDPRingMap_dp]
  rfl

end Principal
end SerrePositivity.BhattScholze.Andre

end PrincipalDPIdealQuotient

/-! ## 正則一元入力の mod p 一次関係商の実分冪構造

## 概要

p 正則・p 局所 δ 環の元 y が mod p で非零因子なら、mod p 一次関係商の
正次数生成元イデアルに実際の分冪構造を構成する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の明示計算の分冪構造側。

## 方針

階乗部分環の mod p 分冪構造を既存の具体的な環同型で移す。
正次数イデアルは全正次数標準分冪生成元の生成イデアルと同定する。

## 規約

δ 環からの持ち上げ、p 正則性・p 局所性・mod p 正則性を全て明示する。
任意の正標数環上で無条件の構造を宣言するものではない。

## 使われ方

既存の分冪標的への普遍射と合わせ、正則入力の実 pd 包の普遍性を得る。
-/

@[expose] public noncomputable section RegularPrincipalModPrimeDividedPowers

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：一次関係商内の正次数分冪生成元で生成されるイデアル。
方針：次数 n+1 の標準生成元全体の span を取る。
規約：係数環と入力元を固定し、分冪構造の存在は定義に含めない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包のイデアルの指定。 -/
def principalDPPositiveIdeal (y : A) : Ideal (PrincipalDPPresentation A y) :=
  Ideal.span (Set.range fun n : ℕ => principalDPGenerator y (n + 1))


omit [Fact p.Prime] in
/-- 概要：入力元 y の係数像は一次関係商の正次数生成元イデアルに属する。
方針：一次関係 γ₁=y と零番目の正次数生成元の所属を使う。
規約：この所属自体に正則性や標数は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪値を入力元で評価する。 -/
theorem principalDPPositiveIdeal_base_mem (y : A) :
    algebraMap A (PrincipalDPPresentation A y) y ∈ principalDPPositiveIdeal y := by
  rw [← principalDPGenerator_one]
  exact Ideal.subset_span (Set.mem_range_self 0)

variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A => (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "ys" => fun _ : Unit => y
local notation "S" => pDivisionFactorialSubring p ys
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : S)})
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "e" => regularPrincipalDPFactorialModPEquiv hlocal hpA D y hy

/-- 概要：mod p 正次数階乗イデアルの像は一次関係商の正次数生成元イデアル。
方針：既存比較同型の全階乗生成元上の値を使って span の生成集合を比較する。
規約：実商射と既存の環同型の合成を使用する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪構造の移送。 -/
theorem regularPrincipalModPrime_positiveIdeal_map :
    ((pDivisionFactorialIdeal p ys).map q).map (e).toRingHom =
      principalDPPositiveIdeal (bar y) := by
  rw [Ideal.map_map, pDivisionFactorialIdeal, Ideal.map_span]
  unfold principalDPPositiveIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨⟨s, n⟩, rfl⟩, rfl⟩
    cases s
    exact ⟨n, (regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy (n + 1)).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨pDivisionFactorialValue p ys () (n + 1),
      pDivisionFactorialSubring_value_mem ys () (n + 1)⟩ : S), ?_, ?_⟩
    · exact ⟨((), n), rfl⟩
    · exact regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy (n + 1)

/-- 概要：正則な持ち上げを持つ mod p 一次関係商の正次数イデアルには実分冪構造がある。
方針：階乗部分環の mod p 分冪構造を正次数イデアルの具体的な比較同型で移す。
規約：p 正則な δ 持ち上げと mod p 正則性を前提に残す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正則入力の実 pd 包の構成。 -/
def regularPrincipalModPrimeDividedPowers : DividedPowers (principalDPPositiveIdeal (bar y)) :=
  DividedPowers.ofRingEquiv (regularPrincipalModPrime_positiveIdeal_map hlocal hpA D y hy)
    (factorialModPrimeDividedPowers hlocal D ys)


/-- 概要：実 mod p 分冪構造による入力元の n 次分冪は標準の n 次生成元。
方針：階乗部分環の係数と生成元を保つ比較公式を使い、mod p 分冪値を移す。
規約：全ての n を含み、入力の持ち上げと正則性の仮定は明示したまま。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の普遍射の標準値。 -/
theorem regularPrincipalModPrimeDividedPowers_base_apply (n : ℕ) :
    (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy).dpow n
      (algebraMap (A ⧸ Ideal.span {(p : A)}) _ (bar y)) = principalDPGenerator (bar y) n := by
  rw [← regularPrincipalDPFactorialModPEquiv_coeff hlocal hpA D y hy y]
  rw [regularPrincipalModPrimeDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
  rw [factorialModPrimeDividedPowers_base_apply hlocal D ys () n]
  exact regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy n

end SerrePositivity.BhattScholze.Andre

end RegularPrincipalModPrimeDividedPowers

/-! ## 正次数分冪構造を持つ一次関係商の実普遍性

## 概要

一次関係商の入力元の分冪が全標準生成元と一致するなら、任意の分冪標的へ
係数を保つ分冪射が一意に存在する。BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の普遍性。

## 方針

既存の通常代数の評価射が分冪射であることを正次数生成元上で確認する。
一意性は全標準生成元上の外延性に帰着する。

## 規約

分冪構造と入力元の値の公式を明示引数にする。実構造の存在は前工程で別に証明する。
標的のねじれ・正則性・δ 構造は要求しない。

## 使われ方

正則な δ 持ち上げから得た実 mod p 分冪構造を、pd 包の普遍性と結び付ける。
-/

@[expose] public noncomputable section PrincipalDPPositiveUniversal

namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
variable (Hs : DividedPowers (principalDPPositiveIdeal y))
variable (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
  principalDPGenerator y n)
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (Ht : DividedPowers I) (hyB : algebraMap A B y ∈ I)

include hγ hyB

/-- 概要：一次関係商の標準評価は実際の分冪射である。
方針：正次数生成元上で分冪の合成則と入力元の値の公式を比較する。
規約：標的には任意の p ねじれを許し、素数も指定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の存在側の普遍射。 -/
theorem principalDPEval_positive_isDPMorphism :
    Hs.IsDPMorphism Ht (principalDPEval Ht y hyB).toRingHom := by
  have hbase := principalDPPositiveIdeal_base_mem y
  apply DividedPowers.IsDPMorphism.on_span Hs Ht
    (S := Set.range fun k : ℕ => principalDPGenerator y (k + 1)) rfl
  · rintro a ⟨k, rfl⟩
    change principalDPEval Ht y hyB (principalDPGenerator y (k + 1)) ∈ I
    rw [principalDPEval_generator]
    exact Ht.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n a ⟨k, rfl⟩
    change principalDPEval Ht y hyB (Hs.dpow n (principalDPGenerator y (k + 1))) =
      Ht.dpow n (principalDPEval Ht y hyB (principalDPGenerator y (k + 1)))
    rw [← hγ (k + 1), Hs.dpow_comp (Nat.succ_ne_zero k) hbase, map_mul, map_natCast,
      hγ (n * (k + 1)), hγ (k + 1), principalDPEval_generator, principalDPEval_generator,
      Ht.dpow_comp (Nat.succ_ne_zero k) hyB]

/-- 概要：一次関係商から任意の分冪標的への係数を保つ分冪射は一意に存在する。
方針：標準評価を存在証人とし、入力元の分冪値から全標準生成元上の一致を得る。
規約：構造と値の公式を前提にし、標的には追加の正則性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の普遍性。 -/
theorem existsUnique_principalDPPositiveMorphism :
    ∃! F : PrincipalDPPresentation A y →ₐ[A] B, Hs.IsDPMorphism Ht F.toRingHom := by
  refine ⟨principalDPEval Ht y hyB, principalDPEval_positive_isDPMorphism y Hs hγ Ht hyB, ?_⟩
  intro F hF
  apply principalDPHom_ext
  intro n
  calc
    F (principalDPGenerator y n) =
        F (Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y)) := congrArg F (hγ n).symm
    _ = Ht.dpow n (F (algebraMap A (PrincipalDPPresentation A y) y)) :=
      (hF.dpow_comp _ (principalDPPositiveIdeal_base_mem y)).symm
    _ = Ht.dpow n (algebraMap A B y) := congrArg (Ht.dpow n) (F.commutes y)
    _ = _ := (principalDPEval_generator Ht y hyB n).symm

end SerrePositivity.BhattScholze.Andre

end PrincipalDPPositiveUniversal

/-! ## 係数同型による実分冪構造と普遍性の移送

## 概要

一次関係商の正次数イデアルの実分冪構造を、入力を保つ係数環同型に沿って移す。
標準分冪値が生成元に一致する公式と pd 普遍性も移る。
BS 著者版 Remark 7.15(1)（著者版 p.62）の実係数比較のための一般補題。

## 方針

商同型の全生成元上の公式で正次数イデアルの像を同定し、
既存の環同型による分冪構造の移送を使う。

## 規約

分冪構造の存在と標準値は元の環から供給する。係数環の標数や正則性は仮定しない。

## 使われ方

実 mod p 商上で構成した分冪包を、係数商上の無限根環の同じ入力へ移す。
-/

@[expose] public noncomputable section PrincipalDPTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable (e : A ≃+* B) (y : A) (z : B) (hy : e y = z)
local notation "F" => principalDPRingEquivOfEq e y z hy

/-- 概要：入力を保つ係数同型は正次数生成元イデアルを保つ。
方針：各正次数標準生成元の像を計算して生成集合を比較する。
規約：対象イデアルは全正次数生成元の span そのもの。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の移送の入力。 -/
theorem principalDPPositiveIdeal_map_equiv :
    (principalDPPositiveIdeal y).map (F).toRingHom = principalDPPositiveIdeal z := by
  rw [principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun n : ℕ => F (principalDPGenerator y (n + 1))) = _
  simp only [principalDPRingEquivOfEq_generator, principalDPPositiveIdeal]

/-- 概要：入力を保つ係数同型で一次関係商の実分冪構造を移せる。
方針：正次数イデアルの像の同定と環同型による既存の分冪移送を使う。
規約：元の環上の分冪構造を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的な係数表示での実 pd 構造。 -/
def principalDPTransportDividedPowers (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    DividedPowers (principalDPPositiveIdeal z) :=
  DividedPowers.ofRingEquiv (principalDPPositiveIdeal_map_equiv e y z hy) Hs

/-- 概要：移送した構造でも入力元の n 次分冪は n 次標準生成元。
方針：入力係数の比較と環同型による分冪作用の公式を使う。
規約：元の構造についての標準値公式を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の移送後の実 pd 普遍性への入力。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数同型後の実 pd 包。 -/
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

end PrincipalDPTransport

/-! ## 正則 δ 持ち上げの mod p 一次関係商の pd 包普遍性

## 概要

正則な δ 持ち上げから構成した実分冪構造を持つ一次関係商は、
任意の分冪標的への係数を保つ分冪射の一意存在を満たす。
BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の普遍性。

## 方針

実分冪構造と、その入力元の分冪が標準生成元に一致する公式を前工程から供給する。

## 規約

持ち上げの p 正則性・p 局所性・δ 構造と、入力元の mod p 正則性は明示する。
分冪構造や値の公式そのものを仮定する必要はない。

## 使われ方

完全 prism 上の正則モニック入力へ適用し、通常の明示表示を実 pd 包へ接続する。
-/

@[expose] public noncomputable section RegularPrincipalModPrimeUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：正則な δ 持ち上げの mod p 一次関係商から、任意の分冪標的への分冪射は一意。
方針：既に構成した実分冪構造と標準生成元公式を一般の一次関係商の普遍性へ渡す。
規約：標的の正則性・δ 構造・完備性は要求しない。持ち上げの仮定は明示したまま。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の通常の普遍性。 -/
theorem existsUnique_regularPrincipalModPrimeDPMorphism
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    {B : Type v} [CommRing B] [Algebra (A ⧸ Ideal.span {(p : A)}) B]
    {I : Ideal B} (Ht : DividedPowers I)
    (hyB : algebraMap (A ⧸ Ideal.span {(p : A)}) B
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) ∈ I) :
    ∃! F : PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) →ₐ[A ⧸ Ideal.span {(p : A)}] B,
      (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _
    (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy)
    (regularPrincipalModPrimeDividedPowers_base_apply hlocal hpA D y hy) Ht hyB

end SerrePositivity.BhattScholze.Andre

end RegularPrincipalModPrimeUniversal

/-! ## 一次関係商と係数 p 乗商上の切断表示

## 概要

一元分冪代数に γ₁=y を課した表示環を、A/(yᵖ) 上の可算切断多項式商と比較する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の明示的な通常環表示。

## 方針

最初の切断変数を y の係数像、後続の変数を残りの切断変数へ送る。
逆向きは後続の素数冪分冪を使う。

## 規約

p は素数で A 内で零。ここで扱うのは一次関係を課した通常環であり、
実 pd 包の分冪構造・普遍性との比較は別工程である。

## 使われ方

原典の A/(yᵖ)[g₁,g₂,…]/(gᵢᵖ) という自由な表示を具体化する。
-/

@[expose] public noncomputable section PrincipalDPTruncatedPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hprime" => (Fact.out : p.Prime)

/-- 概要：係数 y の p 乗商上の可算切断多項式表示環。
方針：既存の切断多項式商の係数環を実商 A/(yᵖ) にする。
規約：変数 i は元の分冪の次数 p^(i+1) に対応する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示表示の右辺。 -/
abbrev PrincipalDPTruncatedPresentation (y : A) :=
  DividedPowerPrimeTruncatedAlgebra (A := A ⧸ Ideal.span {y ^ p}) p

/-- 概要：係数 y と後続の切断変数からなる可算元族。
方針：零番目に係数 y の像、後続に通常の切断変数を置く。
規約：番号を一つずらして一次分冪の関係を取り出す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係を満たす評価。 -/
def principalDPTruncatedRoot (y : A) : ℕ → PrincipalDPTruncatedPresentation p y
  | 0 => algebraMap A _ y
  | i + 1 => Ideal.Quotient.mk _ (MvPolynomial.X i)

omit [Fact p.Prime] in
/-- 概要：係数 y と後続の切断変数はいずれも p 乗が零。
方針：零番目には係数商の関係、後続には切断変数の関係を使う。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の普遍評価射の入力。 -/
theorem principalDPTruncatedRoot_pow (y : A) (i : ℕ) :
    principalDPTruncatedRoot p y i ^ p = 0 := by
  cases i with
  | zero =>
    change Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {y ^ p}) y)) ^ p = 0
    rw [← map_pow, ← map_pow, ← map_pow]
    have hy : Ideal.Quotient.mk (Ideal.span {y ^ p}) (y ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hy, map_zero, map_zero]
  | succ i =>
    exact (monicPowerFamilyQuotient_root_pow p ℕ (A ⧸ Ideal.span {y ^ p})
      (fun _ => 0) i).trans (map_zero _)

/-- 概要：自由分冪代数から係数 p 乗商上の切断表示への標準射。
方針：可算切断表示の逆同型と、指定した p 乗零元族への普遍評価を合成する。
規約：最初の素数冪分冪は係数 y へ送る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係商の順射。 -/
def principalDPToTruncatedRaw (hp : (p : A) = 0) (y : A) :
    DividedPowerAlgebra A A →ₐ[A] PrincipalDPTruncatedPresentation p y :=
  (dividedPowerPrimeTruncatedLift (A := A) p (principalDPTruncatedRoot p y)
    (principalDPTruncatedRoot_pow p y)).comp (dividedPowerPrimeTruncatedEquiv p hp).symm.toAlgHom

/-- 概要：自由分冪からの射は素数冪分冪を指定した係数・変数族へ送る。
方針：切断表示同型の逆と変数上の普遍評価を使う。
規約：次数は p の自然数冪。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の二射の比較。 -/
theorem principalDPToTruncatedRaw_dp (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPToTruncatedRaw p hp y (DividedPowerAlgebra.dp A (p ^ i) (1 : A)) =
      principalDPTruncatedRoot p y i := by
  rw [← dividedPowerPrimeTruncatedEquiv_X p hp i]
  change dividedPowerPrimeTruncatedLift (A := A) p (principalDPTruncatedRoot p y)
    (principalDPTruncatedRoot_pow p y)
    ((dividedPowerPrimeTruncatedEquiv p hp).symm
      (dividedPowerPrimeTruncatedEquiv p hp (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact dividedPowerPrimeTruncatedLift_X p _ (principalDPTruncatedRoot_pow p y) i

/-- 概要：一次関係商から係数 p 乗商上の切断表示への標準射。
方針：一次分冪を y に送ることを使い、自由分冪代数からの射を商に降ろす。
規約：係数環 A の作用を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の順射。 -/
def principalDPToTruncated (hp : (p : A) = 0) (y : A) :
    PrincipalDPPresentation A y →ₐ[A] PrincipalDPTruncatedPresentation p y := by
  apply Ideal.Quotient.liftₐ _ (principalDPToTruncatedRaw p hp y)
  have hker : principalDPRelationIdeal y ≤ RingHom.ker (principalDPToTruncatedRaw p hp y) := by
    apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change principalDPToTruncatedRaw p hp y
      (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y) = 0
    rw [map_sub, show (1 : ℕ) = p ^ 0 by simp, principalDPToTruncatedRaw_dp, AlgHom.commutes]
    exact sub_self _
  exact fun _ hx => hker hx

/-- 概要：一次関係商の素数冪分冪の標準像を指定した元族へ送る。
方針：商への降下前の評価公式を使う。
規約：零番目の値は係数 y である。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の逆合成の確認。 -/
theorem principalDPToTruncated_generator (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPToTruncated p hp y (principalDPGenerator y (p ^ i)) =
      principalDPTruncatedRoot p y i :=
  principalDPToTruncatedRaw_dp p hp y i

/-- 概要：一次関係商の全素数冪分冪生成元は p 乗が零。
方針：自由分冪代数の消滅式を商射で移す。
規約：入力 y の正則性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断商の普遍射の入力。 -/
theorem principalDPPrimeGenerator_pow_zero (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPGenerator y (p ^ i) ^ p = 0 := by
  change (Ideal.Quotient.mk (principalDPRelationIdeal y)
    (DividedPowerAlgebra.dp A (p ^ i) (1 : A))) ^ p = 0
  rw [← map_pow, dividedPowerPrimePower_pow_zero p hp, map_zero]

/-- 概要：係数 p 乗商上の切断表示から一次関係商への標準射。
方針：既存の係数商作用を使い、変数 i を次数 p^(i+1) の分冪の像に送る。
規約：元の A 作用とのスカラー塔を明示してから制限する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の逆射。 -/
def principalDPTruncatedToPresentation (hp : (p : A) = 0) (y : A) :
    PrincipalDPTruncatedPresentation p y →ₐ[A] PrincipalDPPresentation A y := by
  letI := principalDPQuotientAlgebra (hprime).pos hp y
  letI := principalDPQuotient_isScalarTower (hprime).pos hp y
  exact (dividedPowerPrimeTruncatedLift (A := A ⧸ Ideal.span {y ^ p}) p
    (fun i => principalDPGenerator y (p ^ (i + 1)))
    (fun i => principalDPPrimeGenerator_pow_zero p hp y (i + 1))).restrictScalars A

/-- 概要：逆向きの標準射は変数 i を次数 p^(i+1) の分冪の像へ送る。
方針：切断商の普遍射の変数公式を使う。
規約：最初の変数は次数 p の分冪を表す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の逆合成の検証。 -/
theorem principalDPTruncatedToPresentation_X (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPTruncatedToPresentation p hp y (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      principalDPGenerator y (p ^ (i + 1)) := by
  let := principalDPQuotientAlgebra (hprime).pos hp y
  let := principalDPQuotient_isScalarTower (hprime).pos hp y
  exact dividedPowerPrimeTruncatedLift_X (A := A ⧸ Ideal.span {y ^ p}) p
    (fun i => principalDPGenerator y (p ^ (i + 1)))
    (fun i => principalDPPrimeGenerator_pow_zero p hp y (i + 1)) i


omit [Fact p.Prime] in
/-- 概要：係数 p 乗商上の切断表示からの A 代数射は変数の値で決まる。
方針：係数商の各元を A から持ち上げ、係数上は代数射の可換性を使う。
規約：終域に係数商上の代数構造は要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の二射の逆合成の検証。 -/
theorem principalDPTruncatedHom_ext {B : Type u} [CommRing B] [Algebra A B] (y : A)
    (f g : PrincipalDPTruncatedPresentation p y →ₐ[A] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply AlgHom.toRingHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change f (algebraMap A _ a) = g (algebraMap A _ a)
    exact (f.commutes a).trans (g.commutes a).symm
  · exact h

/-- 概要：一次関係商から切断表示へ移して戻すと恒等射になる。
方針：素数冪分冪の像で比較し、次数一では一次関係、後続では変数公式を使う。
規約：係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示表示同型の検証。 -/
theorem principalDPTruncatedToPresentation_comp_toTruncated (hp : (p : A) = 0) (y : A) :
    (principalDPTruncatedToPresentation p hp y).comp (principalDPToTruncated p hp y) =
      AlgHom.id A _ := by
  apply principalDPPrimeHom_ext p hp y
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, principalDPToTruncated_generator]
  cases i with
  | zero =>
    change principalDPTruncatedToPresentation p hp y (algebraMap A _ y) =
      principalDPGenerator y 1
    rw [AlgHom.commutes, principalDPGenerator_one]
  | succ i => exact principalDPTruncatedToPresentation_X p hp y i

/-- 概要：切断表示から一次関係商へ移して戻しても恒等射になる。
方針：切断変数上の外延性と両方向の生成元の公式を使う。
規約：元の A 係数作用を保つ射として述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示表示同型の検証。 -/
theorem principalDPToTruncated_comp_truncatedToPresentation (hp : (p : A) = 0) (y : A) :
    (principalDPToTruncated p hp y).comp (principalDPTruncatedToPresentation p hp y) =
      AlgHom.id A _ := by
  apply principalDPTruncatedHom_ext
  intro i
  change principalDPToTruncated p hp y
    (principalDPTruncatedToPresentation p hp y (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
  rw [principalDPTruncatedToPresentation_X, principalDPToTruncated_generator]
  rfl

/-- 概要：γ₁=y の一元分冪表示環は係数商 A/(yᵖ) 上の可算切断表示と A 代数同型。
方針：素数冪分冪と切断変数で照合した互いに逆な二射を束ねる。
規約：実 pd 包との同定はこの通常代数同型に含まない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示的な自由表示。 -/
def principalDPTruncatedEquiv (hp : (p : A) = 0) (y : A) :
    PrincipalDPPresentation A y ≃ₐ[A] PrincipalDPTruncatedPresentation p y :=
  AlgEquiv.ofAlgHom (principalDPToTruncated p hp y) (principalDPTruncatedToPresentation p hp y)
    (principalDPToTruncated_comp_truncatedToPresentation p hp y)
    (principalDPTruncatedToPresentation_comp_toTruncated p hp y)

/-- 概要：表示同型は次数 p^(i+1) の分冪の標準像を i 番目の切断変数へ送る。
方針：同型の順射の生成元公式を使う。
規約：一次分冪は係数に移り、変数は次の素数冪から始まる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の原典の g₁,g₂,… との対応。 -/
theorem principalDPTruncatedEquiv_generator_succ (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPTruncatedEquiv p hp y (principalDPGenerator y (p ^ (i + 1))) =
      Ideal.Quotient.mk _ (MvPolynomial.X i) :=
  principalDPToTruncated_generator p hp y (i + 1)


/-- 概要：一次関係商と切断表示の同型は既存の係数商 A/(yᵖ) 作用を保つ。
方針：係数商の代表元を A から持ち上げ、標準係数商射の値と A 代数同型の可換性を使う。
規約：一次関係商側の作用は既存の principalDPQuotientAlgebra をそのまま使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商からの自由拡大の表示。 -/
def principalDPTruncatedQuotientAlgEquiv (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (hprime).pos hp y
    PrincipalDPPresentation A y ≃ₐ[A ⧸ Ideal.span {y ^ p}]
      PrincipalDPTruncatedPresentation p y := by
  letI := principalDPQuotientAlgebra (hprime).pos hp y
  refine { (principalDPTruncatedEquiv p hp y).toRingEquiv with commutes' := ?_ }
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change principalDPTruncatedEquiv p hp y
    (principalDPQuotientMap (hprime).pos hp y (Ideal.Quotient.mk _ a)) = algebraMap A _ a
  rw [principalDPQuotientMap_mk]
  exact (principalDPTruncatedEquiv p hp y).commutes a


/-- 概要：係数 p 乗商上の可算切断表示はその係数環上自由。
方針：既存のモニック冪関係商と通常根添加環の同型で自由性を移す。
規約：零係数商を含み、y の正則性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示表示の自由性。 -/
theorem principalDPTruncatedPresentation_free (y : A) :
    Module.Free (A ⧸ Ideal.span {y ^ p}) (PrincipalDPTruncatedPresentation p y) := by
  let B := A ⧸ Ideal.span {y ^ p}
  let := monicPowerFamilyCover_moduleFree p ℕ B (fun _ => 0) (hprime).pos
  exact Module.Free.of_equiv
    (monicPowerFamilyPresentationAlgEquiv p ℕ B (fun _ => 0)).symm.toLinearEquiv

/-- 概要：一次関係商は既存の係数商 A/(yᵖ) 作用について自由。
方針：具体的切断表示の自由性を係数商上の代数同型で戻す。
規約：作用は既存の principalDPQuotientAlgebra を固定し、補助平坦性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示表示による自由性の証明。 -/
theorem principalDPPresentation_free_via_truncated (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (hprime).pos hp y
    Module.Free (A ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation A y) := by
  let := principalDPQuotientAlgebra (hprime).pos hp y
  let := principalDPTruncatedPresentation_free p y
  exact Module.Free.of_equiv (principalDPTruncatedQuotientAlgEquiv p hp y).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PrincipalDPTruncatedPresentation

/-! ## 正次数分冪イデアルによる商と元の入力商

## 概要

γ₁=y の一元分冪表示環を全正次数生成元のイデアルで割ると A/(y) に A 代数同型。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更で実分冪構造を降ろすための計算。

## 方針

零イデアルの分冪構造への評価で augmentation を構成し、係数からの逆射を作る。
逆合成は係数と全標準生成元上で確認する。

## 規約

係数環の標数・正則性・非零性も、表示環自身の分冪構造も要求しない。

## 使われ方

モニック入力商の自由性から正次数イデアルによる商の平坦性を得て、係数変更を制御する。
-/

@[expose] public noncomputable section PrincipalDPPositiveQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
local notation "D" => PrincipalDPPresentation A y
local notation "J" => principalDPPositiveIdeal y
local notation "R" => A ⧸ Ideal.span {(y : A)}

/-- 概要：入力 y の係数像は実入力商 A/(y) で零。
方針：入力元が定義の主イデアルに属することを使う。
規約：標準の係数商射を使用する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の augmentation の入力。 -/
theorem principalDPInputQuotient_input_eq_zero : algebraMap A R y = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：一次関係商から元の入力商への augmentation。
方針：標的の零イデアルの分冪構造へ標準評価する。
規約：係数環 A の作用を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数商の同定。 -/
def principalDPAugmentation : D →ₐ[A] R :=
  principalDPEval (dividedPowersBot R) y
    (Ideal.mem_bot.mpr (principalDPInputQuotient_input_eq_zero y))

/-- 概要：augmentation は全正次数標準生成元を零へ送る。
方針：零イデアル内の正次数分冪は零であることを使う。
規約：次数は n+1 とする。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数商への降下。 -/
theorem principalDPAugmentation_generator_succ (n : ℕ) :
    principalDPAugmentation y (principalDPGenerator y (n + 1)) = 0 := by
  rw [principalDPAugmentation, principalDPEval_generator]
  exact Ideal.mem_bot.mp ((dividedPowersBot R).dpow_mem (Nat.succ_ne_zero n)
    (Ideal.mem_bot.mpr (principalDPInputQuotient_input_eq_zero y)))

/-- 概要：augmentation は正次数イデアルによる商から入力商へ降りる。
方針：正次数生成元を全て零に送るので商の普遍射を使う。
規約：実際の正次数イデアル J の商を取る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の商同型の順射。 -/
def principalDPPositiveQuotientToInput : (D ⧸ J) →ₐ[A] R := by
  apply Ideal.Quotient.liftₐ _ (principalDPAugmentation y)
  have hker : J ≤ RingHom.ker (principalDPAugmentation y).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact principalDPAugmentation_generator_succ y n
  exact fun _ hx => hker hx

/-- 概要：正次数商からの augmentation は代表元で元の augmentation と一致。
方針：商の普遍射の代表元公式を使う。
規約：全ての表示環の元で述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の逆合成の検証。 -/
theorem principalDPPositiveQuotientToInput_mk (x : D) :
    principalDPPositiveQuotientToInput y (Ideal.Quotient.mk J x) =
      principalDPAugmentation y x := rfl

/-- 概要：入力商 A/(y) から正次数分冪商への標準係数射。
方針：入力 y が正次数イデアルに属すので係数射を入力商へ降ろす。
規約：元の A 係数作用を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の商同型の逆射。 -/
def principalDPInputToPositiveQuotient : R →ₐ[A] D ⧸ J := by
  apply Ideal.Quotient.liftₐ _ (Algebra.ofId A (D ⧸ J))
  have hker : Ideal.span {y} ≤ RingHom.ker (Algebra.ofId A (D ⧸ J)).toRingHom := by
    apply Ideal.span_le.mpr
    intro t ht
    have hty : t = y := Set.mem_singleton_iff.mp ht
    subst t
    change Ideal.Quotient.mk J (algebraMap A D y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (principalDPPositiveIdeal_base_mem y)
  exact fun _ hx => hker hx

/-- 概要：入力商からの標準射は元の係数を同じ正次数商の係数へ送る。
方針：商への降下の定義を使う。
規約：任意の元 a の商代表元で述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数上の逆合成。 -/
theorem principalDPInputToPositiveQuotient_mk (a : A) :
    principalDPInputToPositiveQuotient y (Ideal.Quotient.mk _ a) = algebraMap A (D ⧸ J) a := rfl

/-- 概要：入力商から正次数商へ移して戻すと恒等射。
方針：入力商の係数代表元上で代数射の可換性を使う。
規約：係数環 A を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の商同型の検証。 -/
theorem principalDPPositiveQuotientToInput_comp_inputToPositive :
    (principalDPPositiveQuotientToInput y).comp (principalDPInputToPositiveQuotient y) =
      AlgHom.id A R := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change principalDPPositiveQuotientToInput y
    (principalDPInputToPositiveQuotient y (Ideal.Quotient.mk _ a)) = _
  rw [principalDPInputToPositiveQuotient_mk, AlgHom.commutes]
  rfl

/-- 概要：正次数商から入力商へ移して戻しても恒等射。
方針：零次生成元は単位、正次数生成元は両側とも零であることを使う。
規約：表示環の全標準生成元上で確認する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の商同型の検証。 -/
theorem principalDPInputToPositiveQuotient_comp_positiveToInput :
    (principalDPInputToPositiveQuotient y).comp (principalDPPositiveQuotientToInput y) =
      AlgHom.id A (D ⧸ J) := by
  apply Ideal.Quotient.algHom_ext
  apply principalDPHom_ext
  intro n
  cases n with
  | zero => simp [principalDPGenerator, DividedPowerAlgebra.dp_zero]
  | succ n =>
    change principalDPInputToPositiveQuotient y
      (principalDPPositiveQuotientToInput y
        (Ideal.Quotient.mk J (principalDPGenerator y (n + 1)))) =
        Ideal.Quotient.mk J (principalDPGenerator y (n + 1))
    rw [principalDPPositiveQuotientToInput_mk, principalDPAugmentation_generator_succ, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self n))

/-- 概要：一次関係商を正次数分冪イデアルで割ると元の入力商 A/(y) と A 代数同型。
方針：互いに逆と確認した augmentation と係数射を束ねる。
規約：係数環の標数や正則性は要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更での平坦性とイデアル交わりの制御。 -/
def principalDPPositiveQuotientEquiv : (D ⧸ J) ≃ₐ[A] R :=
  AlgEquiv.ofAlgHom (principalDPPositiveQuotientToInput y) (principalDPInputToPositiveQuotient y)
    (principalDPPositiveQuotientToInput_comp_inputToPositive y)
    (principalDPInputToPositiveQuotient_comp_positiveToInput y)

end SerrePositivity.BhattScholze.Andre

end PrincipalDPPositiveQuotient
