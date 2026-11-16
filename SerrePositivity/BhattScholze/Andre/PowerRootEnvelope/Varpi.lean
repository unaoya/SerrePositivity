module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DividedPowerPrime

/-!
# ϖ の選択と ϖ 商（BS 著者版 Remark 7.15）

## 概要
モニック入力の mod p 分冪包と分冪表示環の忠実平坦性、完全 prism 上の mod p 分冪包、完全 prism の生成元から ϖ（ϖᵖ と p が単元倍で等しい元）を選ぶこと、ϖ 商から p 商への Frobenius 同型と逆 Frobenius。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Completion`、`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/PowerRootInput`、`PowerRootEnvelope/VarpiPD`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## 完全 prism の生成元から選ぶ ϖ

## 概要

完全 prism (A,(d)) で x=φ⁻¹(d) と置く。R=A/(d) 内の像 ϖ は (ϖ^p)=(p) を満たす。
さらに A 内で (d,x)=(p,x) となる。
BS 著者版 Remark 7.15（著者版 p.62）の係数商の比較に必要な具体的な選択である。

## 方針

逆 Frobenius が δ 射なので δ(x) は単元。d=x^p+pδ(x) を商へ移す。

## 規約

prism の指定生成元を使用する。R の p 正則性はここでは仮定しない。

## 使われ方

原典の R/ϖ と A/(p,x) の比較への入力。prismatic envelope の同定は主張しない。
-/

@[expose] public noncomputable section PerfectPrismVarpi

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：prism 生成元の Frobenius 逆像を選ぶ。
方針：完全 δ 環の Frobenius 同型の逆を使う。
規約：指定生成元を使用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の ϖ の持上げ。 -/
def perfectPrismVarpiLift (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) : A :=
  (W.deltaStructure.frobeniusEquiv hW).symm W.generator

/-- 概要：選んだ持上げの Frobenius は prism 生成元。
方針：環同型の逆合成を使う。
規約：等式は A 内で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数計算。 -/
theorem perfectPrismVarpiLift_frobenius (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    W.deltaStructure.frobeniusLift (perfectPrismVarpiLift W hW) = W.generator :=
  (W.deltaStructure.frobeniusEquiv hW).apply_symm_apply W.generator

/-- 概要：ϖ の持上げは distinguished 元。
方針：生成元の distinguished 性を逆 Frobenius の δ 射で移す。
規約：単元性は A 内で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p と ϖ^p の比較。 -/
theorem perfectPrismVarpiLift_delta_isUnit (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    IsUnit (W.deltaStructure.delta (perfectPrismVarpiLift W hW)) := by
  have h := (W.isDistinguished_generator).map
    (W.deltaStructure.frobeniusEquiv hW).symm.toRingHom
  change IsUnit ((W.deltaStructure.frobeniusEquiv hW).symm.toRingHom
    (W.deltaStructure.delta W.generator)) at h
  rw [W.deltaStructure.frobeniusEquiv_symm_isDeltaHom hW W.generator] at h
  exact h

/-- 概要：ϖ は Frobenius 逆像の prism 商への像。
方針：指定 prism イデアルの標準商射を使う。
規約：台環は A/(d)。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数元。 -/
def perfectPrismVarpi (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    A ⧸ W.ideal := Ideal.Quotient.mk W.ideal (perfectPrismVarpiLift W hW)

/-- 概要：選んだ ϖ の p 乗は p と明示的な単元の積。
方針：φ(x)=x^p+pδ(x)=d を prism 商へ移す。
規約：単元因子は −δ(x) の商像。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の (ϖ^p)=(p)。 -/
theorem perfectPrismVarpi_pow (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    perfectPrismVarpi W hW ^ p = (p : A ⧸ W.ideal) *
      (-Ideal.Quotient.mk W.ideal (W.deltaStructure.delta (perfectPrismVarpiLift W hW))) := by
  have h := congrArg (Ideal.Quotient.mk W.ideal) (perfectPrismVarpiLift_frobenius W hW)
  rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast] at h
  have hd : Ideal.Quotient.mk W.ideal W.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [hd] at h
  change perfectPrismVarpi W hW ^ p + _ = 0 at h
  linear_combination h

/-- 概要：ϖ の p 乗と p は同じ主イデアルを生成する。
方針：明示的な積公式と δ(x) の単元性を使う。
規約：R の p ねじれの有無を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の ϖ の条件。 -/
theorem perfectPrismVarpi_span_pow (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    Ideal.span {perfectPrismVarpi W hW ^ p} = Ideal.span {(p : A ⧸ W.ideal)} := by
  rw [perfectPrismVarpi_pow]
  exact Ideal.span_singleton_mul_right_unit
    (((perfectPrismVarpiLift_delta_isUnit W hW).map (Ideal.Quotient.mk W.ideal)).neg) _

/-- 概要：distinguished 元 x について (φ(x),x)=(p,x)。
方針：φ(x)−x^p=pδ(x) と単元 δ(x) による主イデアルの不変性を使う。
規約：δ 環の完全性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの係数商の比較。 -/
theorem distinguished_frobenius_pair_span (D : DeltaStructure p A) (x : A)
    (hx : IsUnit (D.delta x)) :
    Ideal.span {D.frobeniusLift x, x} = Ideal.span {(p : A), x} := by
  have hpow : x ^ p = x * x ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.Prime.one_le (Fact.out : p.Prime))]
  rw [D.frobeniusLift_apply, hpow, Ideal.span_pair_right_mul_add,
    Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit hx]

/-- 概要：prism 生成元と ϖ の持上げの二元イデアルは (p,x)。
方針：逆 Frobenius 像が distinguished であることを一般 δ 計算へ適用する。
規約：等式は A のイデアルとして述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ の実係数商。 -/
theorem perfectPrismVarpiLift_pair_span (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    Ideal.span {W.generator, perfectPrismVarpiLift W hW} =
      Ideal.span {(p : A), perfectPrismVarpiLift W hW} := by
  rw [← perfectPrismVarpiLift_frobenius W hW]
  exact distinguished_frobenius_pair_span _ _ (perfectPrismVarpiLift_delta_isUnit W hW)

/-- 概要：主イデアルによる二重商を二元イデアルによる商と同一視する。
方針：二重商の標準同型と主イデアルの像の公式を使う。
規約：元の環の代表元を保つ同型を選ぶ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数商比較。 -/
def principalDoubleQuotEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b}) ≃+*
      A ⧸ Ideal.span {a, b} :=
  ((Ideal.quotEquivOfEq (show
      Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b} =
        (Ideal.span {b}).map (Ideal.Quotient.mk (Ideal.span {a})) by
      rw [Ideal.map_span, Set.image_singleton])).trans
    (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.span {b}))).trans
      (Ideal.quotEquivOfEq (Ideal.span_insert a {b}).symm)

/-- 概要：主イデアル二重商の同型は同じ代表元を送る。
方針：標準二重商同型の計算規則を使う。
規約：元は元の環 A で指定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数射の照合。 -/
theorem principalDoubleQuotEquiv_mk (a b t : A) :
    principalDoubleQuotEquiv a b (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) =
      Ideal.Quotient.mk _ t := by
  simp only [principalDoubleQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rw [show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t) =
    DoubleQuot.quotQuotMk (Ideal.span {a}) (Ideal.span {b}) t from rfl,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 概要：prism 商の ϖ 還元は A/p の x 還元と環同型。
方針：両二重商を (d,x)=(p,x) による商へ写す。
規約：x は指定生成元の Frobenius 逆像。正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ 係数。 -/
def perfectPrismVarpiQuotientEquiv (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    ((A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}) ≃+*
      ((A ⧸ Ideal.span {(p : A)}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)}) :=
  ((principalDoubleQuotEquiv W.generator (perfectPrismVarpiLift W hW)).trans
    (Ideal.quotEquivOfEq (perfectPrismVarpiLift_pair_span W hW))).trans
      (principalDoubleQuotEquiv (p : A) (perfectPrismVarpiLift W hW)).symm

/-- 概要：係数商同型は A から来る代表元を保つ。
方針：二重商同型の代表元公式を両側で使う。
規約：同型の向きは R/ϖ から (A/p)/(x)。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式係数比較。 -/
theorem perfectPrismVarpiQuotientEquiv_mk (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) (t : A) :
    perfectPrismVarpiQuotientEquiv W hW (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t) := by
  apply (principalDoubleQuotEquiv (p : A) (perfectPrismVarpiLift W hW)).injective
  simp only [perfectPrismVarpiQuotientEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, principalDoubleQuotEquiv_mk]
  change (Ideal.quotEquivOfEq _)
    ((principalDoubleQuotEquiv W.generator (perfectPrismVarpiLift W hW))
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t))) = _
  rw [principalDoubleQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpi

/-! ## モニック入力の実 mod p 分冪包

## 概要

p 正則・p 局所 δ 係数環上のモニック多項式を独立変数で評価した入力に対し、
mod p 一次関係商の実分冪構造と普遍性を構成する。
BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力への適用。

## 方針

多項式環の自由性から p 正則性、モニック性から mod p 正則性を供給し、
正則持ち上げの実分冪構造と普遍性を適用する。

## 規約

多項式環の mod p 商をそのまま使う。無限 p 冪根変数や prismatic Frobenius 引戻しの
比較をこのファイルだけで主張しない。

## 使われ方

完全 prism 上の入力から、実 pd 包の表示と通常の忠実平坦性へ接続する。
-/

@[expose] public noncomputable section MonicModPrimePDEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type u}

/-- 概要：p が Jacobson 根基に属すれば p と互いに素な自然数は単元。
方針：Bezout 等式の p 項を Jacobson 根基へ移し、残りの積の単元性を得る。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の完全 prism から p 局所性を供給する。 -/
theorem primeLocal_of_prime_mem_jacobson (hJac : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A) := by
  intro m hm
  obtain ⟨a, b, hab⟩ := (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hm).cast
    (R := A)
  have hunit : IsUnit (b * (m : A)) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    have he : b * (m : A) - 1 = -(a * (p : A)) := by
      rw [← hab]
      ring
    rw [he]
    exact (Ideal.jacobson (⊥ : Ideal A)).neg_mem
      ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_left a hJac)
  exact isUnit_of_mul_isUnit_right hunit

omit [Fact p.Prime] in
/-- 概要：係数環で p が正則なら多変数多項式環でも正則。
方針：多項式環の自由性による平坦性で正則性を移す。
規約：変数族の有限性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正則持ち上げの入力。 -/
theorem monicPolynomialRing_primeRegular
    (hpA : Function.Injective (fun a : A => (p : A) * a)) :
    Function.Injective (fun a : MvPolynomial σ A => (p : MvPolynomial σ A) * a) := by
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := MvPolynomial σ A)

omit [Fact p.Prime] in
/-- 概要：p 局所な係数環上の多項式環も p 局所。
方針：自然数の単元を係数射で送る。
規約：多項式の単元全体の分類は使わない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の階乗計算の入力。 -/
theorem monicPolynomialRing_primeLocal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : MvPolynomial σ A) := by
  intro m hm
  simpa only [map_natCast] using (hlocal m hm).map (MvPolynomial.C : A →+* MvPolynomial σ A)

local notation "B" => MvPolynomial σ A
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Q" => B ⧸ Ideal.span {(p : B)}

/-- 概要：モニック関係の mod p 一次関係商の台環。
方針：モニック多項式の指定変数での評価を実 mod p 商に送り、分冪表示環を取る。
規約：この台環の定義にはモニック性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の候補。 -/
abbrev MonicModPrimePDEnvelope (f : Polynomial A) (s : σ) :=
  PrincipalDPPresentation Q (bar (monicRelation f s))

/-- 概要：モニック入力の mod p 表示環の正次数イデアルに実分冪構造がある。
方針：多項式環の p 正則性・p 局所性とモニック関係の mod p 正則性を内部で供給する。
規約：係数環の p 正則性・p 局所性と δ 構造は明示する。正次数は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の実 pd 包。 -/
def monicModPrimePDDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ) :
    DividedPowers (principalDPPositiveIdeal (bar (monicRelation f s))) :=
  regularPrincipalModPrimeDividedPowers (monicPolynomialRing_primeLocal hlocal)
    (monicPolynomialRing_primeRegular hpA) (polynomialRankOneDeltaStructure σ D)
    (monicRelation f s) (monicRelation_modP_isSMulRegular p f hf s)

/-- 概要：モニック入力の実分冪構造では入力元の n 次分冪が標準生成元に一致。
方針：正則入力の評価公式へ具体的なモニック入力を代入する。
規約：n=0 を含める。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の普遍性と明示表示の照合。 -/
theorem monicModPrimePDDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ) (n : ℕ) :
    (monicModPrimePDDividedPowers hlocal hpA D f hf s).dpow n
      (algebraMap Q _ (bar (monicRelation f s))) =
      principalDPGenerator (bar (monicRelation f s)) n :=
  regularPrincipalModPrimeDividedPowers_base_apply (monicPolynomialRing_primeLocal hlocal)
    (monicPolynomialRing_primeRegular hpA) (polynomialRankOneDeltaStructure σ D)
    (monicRelation f s) (monicRelation_modP_isSMulRegular p f hf s) n

/-- 概要：モニック入力の実 mod p 分冪包から任意の分冪標的への射は一意に存在する。
方針：構成した実分冪構造と標準生成元公式を一次関係商の普遍性へ渡す。
規約：標的の p ねじれ・正則性・δ 構造・完備性には条件を置かない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包のモニック入力への適用。 -/
theorem existsUnique_monicModPrimePDMorphism
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (monicRelation f s)) ∈ I) :
    ∃! F : MonicModPrimePDEnvelope (p := p) f s →ₐ[Q] T,
      (monicModPrimePDDividedPowers hlocal hpA D f hf s).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _ (monicModPrimePDDividedPowers hlocal hpA D f hf s)
    (monicModPrimePDDividedPowers_base_apply hlocal hpA D f hf s) Ht hyT

end SerrePositivity.BhattScholze.Andre

end MonicModPrimePDEnvelope

/-! ## 完全 prism 上のモニック入力の実 mod p 分冪包

## 概要

完全 prism の係数環上のモニック関係に対して、mod p 実分冪構造と普遍性を得る。
その台環は入力の p 乗商上の可算切断多項式商であり、係数商上自由。
BS 著者版 Remark 7.15(1)（著者版 p.62）の完全 prism 上のモニック入力の計算。

## 方針

完全性から p 正則性、p 完備性と Jacobson 根基から p 局所性を供給する。
台環の表示には一次関係商の既存の切断同型を用いる。

## 規約

このファイルの変数は通常多項式変数である。無限 p 冪根変数への移行と
prismatic envelope の Frobenius 引戻しとの比較は別工程。

## 使われ方

原典の実 pd 包の明示表示と、prismatic envelope の剰余の同定を接続する。
-/

@[expose] public noncomputable section PerfectPrismMonicModPrimePDEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 概要：完全 prism の係数環は p 局所。
方針：p 完備性から p の Jacobson 根基への所属を得て、Bezout の単元補題を使う。
規約：完備性の仮定は追加せず完全 prism から供給する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の階乗計算の実入力。 -/
theorem perfectPrism_primeLocal (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A) := by
  let := P.isAdicComplete_p_of_perfect hP
  exact primeLocal_of_prime_mem_jacobson
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

local notation "B" => MvPolynomial σ A
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Q" => B ⧸ Ideal.span {(p : B)}

/-- 概要：完全 prism 上のモニック入力の mod p 表示環には実分冪構造がある。
方針：p 正則性と p 局所性を完全 prism から供給し、モニック入力の構造を適用する。
規約：補助的な持ち上げの正則性を仮定として残さない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の完全 prism 上の実 pd 包。 -/
def perfectPrismMonicModPrimeDividedPowers
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : σ) :
    DividedPowers (principalDPPositiveIdeal (bar (monicRelation f s))) :=
  monicModPrimePDDividedPowers (perfectPrism_primeLocal P hP) hP.p_mul_injective
    P.deltaStructure f hf s

/-- 概要：完全 prism 上のモニック入力の実 mod p 分冪包の普遍射は一意に存在する。
方針：持ち上げの各入力を完全 prism とモニック性から内部で供給する。
規約：標的のねじれ・正則性・δ 構造・完備性は仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の実 pd 普遍性。 -/
theorem existsUnique_perfectPrismMonicModPrimePDMorphism
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : σ)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (monicRelation f s)) ∈ I) :
    ∃! F : MonicModPrimePDEnvelope (p := p) f s →ₐ[Q] T,
      (perfectPrismMonicModPrimeDividedPowers P hP f hf s).IsDPMorphism Ht F.toRingHom :=
  existsUnique_monicModPrimePDMorphism (perfectPrism_primeLocal P hP) hP.p_mul_injective
    P.deltaStructure f hf s Ht hyT

omit [Fact p.Prime] in
/-- 概要：実 mod p 多項式係数商では p は零。
方針：p が定義の主イデアルに属することを使う。
規約：係数環の標数自体には条件を置かない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正標数の切断表示への入力。 -/
theorem monicModPrimeCoefficient_prime_eq_zero : (p : Q) = 0 := by
  change Ideal.Quotient.mk (Ideal.span {(p : B)}) (p : B) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：モニック入力の mod p 分冪包の台環は入力の p 乗商上の可算切断表示。
方針：同じ一次関係商の係数商上の具体的同型を使う。
規約：台環の同型自体にはモニック性や prism は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の明示表示。 -/
def monicModPrimePDEnvelope_truncatedEquiv (f : Polynomial A) (s : σ) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos
      (monicModPrimeCoefficient_prime_eq_zero (σ := σ) (A := A) (p := p))
      (bar (monicRelation f s))
    MonicModPrimePDEnvelope (p := p) f s ≃ₐ[Q ⧸ Ideal.span {(bar (monicRelation f s)) ^ p}]
      PrincipalDPTruncatedPresentation p (bar (monicRelation f s)) :=
  principalDPTruncatedQuotientAlgEquiv p monicModPrimeCoefficient_prime_eq_zero _

/-- 概要：モニック入力の実 mod p 分冪包の台環は入力の p 乗係数商上自由。
方針：明示切断表示を介した自由性を同じ係数商作用に適用する。
規約：分冪構造の存在にはモニック性を使うが、この台加群の自由性には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の自由性。 -/
theorem monicModPrimePDEnvelope_quotient_free (f : Polynomial A) (s : σ) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos
      (monicModPrimeCoefficient_prime_eq_zero (σ := σ) (A := A) (p := p))
      (bar (monicRelation f s))
    Module.Free (Q ⧸ Ideal.span {(bar (monicRelation f s)) ^ p})
      (MonicModPrimePDEnvelope (p := p) f s) :=
  principalDPPresentation_free_via_truncated p monicModPrimeCoefficient_prime_eq_zero _

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicModPrimePDEnvelope

/-! ## André：モニック関係式の分冪表示環の忠実平坦性

## 概要

標数 p の係数環 R と正次数モニック f に対し、一変数多項式環内の f の分冪表示環は
元の係数環 R 上忠実平坦である。有限段の変数置換 `Y = Z^n` にも適用する。
BS 著者版 Remark 7.15(1)（p.62）の通常の平坦性の計算に対応する。

## 方針

`R[Y]/(f^p)` のモニック剰余による忠実平坦性と、既存の分冪表示環のこの商上の
忠実平坦性を合成する。元の R の係数作用と整合するスカラー塔を明示する。

## 規約

既存の `PrincipalDPPresentation` を対象とする。実 prismatic envelope の Frobenius
引戻しとの同定は別工程であり、この結果だけで最終目標の忠実平坦性を結論しない。
原典の BS 著者版 Proposition 7.10 による cover 性を引用せず通常代数の計算を行う経路である。

## 使われ方

BS 著者版 Remark 7.15 の pd 計算のうち、有限段の剰余環の忠実平坦性に用いる。
-/

@[expose] public noncomputable section MonicPDFlat

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open Polynomial

/-- 概要：標数 p の係数環上のモニック関係の分冪表示環は元の係数環上自由。
方針：f の p 乗のモニック剰余基底と、その商上の分冪表示環の自由性を合成する。
規約：自由性だけには正次数は不要。実 prismatic envelope との同定を含まない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の自由性の有限段。 -/
theorem monicDPPresentation_free
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) :
    Module.Free R (PrincipalDPPresentation R[X] f) := by
  have hpP : (p : R[X]) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (C : R →+* R[X]) hp
  let := principalDPQuotientAlgebra hprime.pos hpP f
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hpP f
  let : Module.Free R (R[X] ⧸ Ideal.span {f ^ p}) := (hf.pow p).free_adjoinRoot
  let := principalDPPresentation_quotient_free p hprime hpP f
  exact Module.Free.trans (R := R) (S := R[X] ⧸ Ideal.span {f ^ p})
    (M := PrincipalDPPresentation R[X] f)

/-- 概要：標数 p の一般基底に対し、商の忠実平坦性は分冪表示環の忠実平坦性を与える。
方針：商上の既存の忠実平坦性と、元の基底作用を保つスカラー塔を使って合成する。
規約：分冪表示環と実 prismatic envelope の同定は要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 計算を元の基底へ移す。 -/
theorem principalDPPresentation_faithfullyFlat_of_quotient
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B)
    (hQ : Module.FaithfullyFlat R (B ⧸ Ideal.span {y ^ p})) :
    Module.FaithfullyFlat R (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hp y
  let := principalDPQuotient_moduleFaithfullyFlat hprime hp y
  let := hQ
  exact Module.FaithfullyFlat.trans R (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y)

/-- 概要：標数 p の任意可換環上の正次数モニックの分冪表示環は元の係数環上忠実平坦。
方針：f の p 乗のモニック性と正次数で通常商の忠実平坦性を供給する。
規約：係数環の非零性は不要である。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック関係の有限段の計算。 -/
theorem monicDPPresentation_faithfullyFlat
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PrincipalDPPresentation R[X] f) := by
  have hpP : (p : R[X]) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (C : R →+* R[X]) hp
  apply principalDPPresentation_faithfullyFlat_of_quotient p hprime hpP f
  exact adjoinRoot_faithfullyFlat (f ^ p) (hf.pow p) (by
    rw [hf.natDegree_pow]
    exact Nat.mul_pos hprime.pos hdeg)

/-- 概要：正の有限段 `Y = Z^n` におけるモニック関係の分冪表示環も忠実平坦。
方針：expand のモニック性と次数公式を前定理に適用する。
規約：有限段の結果であり、有向余極限や完備化後の結果ではない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根多項式環に至る有限段。 -/
theorem expandedMonicDPPresentation_faithfullyFlat
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) (n : ℕ) (hn : 0 < n) :
    Module.FaithfullyFlat R (PrincipalDPPresentation R[X] (expand R n f)) := by
  apply monicDPPresentation_faithfullyFlat p hprime hp _ (hf.expand hn)
  rw [natDegree_expand]
  exact Nat.mul_pos hdeg hn

end SerrePositivity.BhattScholze.Andre

end MonicPDFlat

/-! ## ϖ 商から p 商への具体的 Frobenius 同型

## 概要

完全 prism (A,(d)) の商 R で、選択した ϖ に対し R/ϖ と R/p は Frobenius で環同型。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しで二つの係数環を追跡する。

## 方針

A の Frobenius 同型は (d,φ⁻¹(d)) を (φ(d),d)=(p,d) へ送る。
二重主イデアル商の同型と合成して代表元上の作用を計算する。

## 規約

順方向は R/ϖ から R/p。prism 商の p 正則性は要求しない。

## 使われ方

raw 除算包の二重剰余と通常 pd 包の係数作用を比較するための具体的な係数同型。
-/

@[expose] public noncomputable section PerfectPrismVarpiFrobeniusQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "D" => W.deltaStructure
local notation "x" => perfectPrismVarpiLift W hW
local notation "R" => A ⧸ W.ideal
local notation "Rv" => R ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => R ⧸ Ideal.span {(p : R)}

/-- 概要：係数 Frobenius は (d,x) を (p,d) へ送る。
方針：φ(x)=d と distinguished 元 d の二元イデアルの計算を使う。
規約：等式は A 内のイデアルの像として述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余係数環の比較。 -/
theorem perfectPrismVarpiFrobenius_pairIdeal :
    (Ideal.span {W.generator, x}).map ((D).frobeniusEquiv hW).toRingHom =
      Ideal.span {(p : A), W.generator} := by
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {(D).frobeniusLift W.generator, (D).frobeniusLift x} = _
  rw [perfectPrismVarpiLift_frobenius]
  exact distinguished_frobenius_pair_span _ _ (W.isDistinguished_generator)

/-- 概要：R/ϖ と R/p の具体的な Frobenius 環同型。
方針：二元商上の係数 Frobenius を二重主イデアル商の同型と合成する。
規約：指定生成元とその逆 Frobenius 像から選んだ ϖ を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 係数作用を明示する。 -/
def perfectPrismVarpiFrobeniusQuotientEquiv : Rv ≃+* Rp :=
  (((principalDoubleQuotEquiv W.generator x).trans
    (Ideal.quotientEquiv _ (Ideal.span {W.generator, (p : A)}) ((D).frobeniusEquiv hW)
      ((Ideal.span_pair_comm).trans (perfectPrismVarpiFrobenius_pairIdeal W hW).symm))).trans
    (principalDoubleQuotEquiv W.generator (p : A)).symm).trans
      (Ideal.quotEquivOfEq (show Ideal.span {Ideal.Quotient.mk W.ideal (p : A)} =
        Ideal.span {(p : R)} by rw [map_natCast]))

/-- 概要：係数商同型は A の代表元に Frobenius を適用する。
方針：二重商と商同型の代表元公式を使う。
規約：順方向の係数作用を全ての b:A で指定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力多項式の係数比較。 -/
theorem perfectPrismVarpiFrobeniusQuotientEquiv_mk (b : A) :
    perfectPrismVarpiFrobeniusQuotientEquiv W hW
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal b)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal ((D).frobeniusLift b)) := by
  have hs : principalDoubleQuotEquiv W.generator x
      (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})
        (Ideal.Quotient.mk W.ideal b)) = Ideal.Quotient.mk _ b := by
    unfold perfectPrismVarpi
    exact principalDoubleQuotEquiv_mk W.generator x b
  have ht := principalDoubleQuotEquiv_mk W.generator (p : A) ((D).frobeniusLift b)
  have ht' := (principalDoubleQuotEquiv W.generator (p : A)).symm_apply_apply
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ ((D).frobeniusLift b)))
  rw [ht] at ht'
  simp only [perfectPrismVarpiFrobeniusQuotientEquiv, RingEquiv.trans_apply]
  erw [hs, Ideal.quotientEquiv_mk]
  change Ideal.quotEquivOfEq _
    ((principalDoubleQuotEquiv W.generator (p : A)).symm
      (Ideal.Quotient.mk _ ((D).frobeniusLift b))) = _
  rw [ht', Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：この係数同型は R の元の p 乗を R/p で取る写像に一致する。
方針：φ(b)=b^p+pδ(b) を二重商へ移し、p の項を消す。
規約：A の代表元で述べ、係数環への非零性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数 Frobenius と通常 p 乗の照合。 -/
theorem perfectPrismVarpiFrobeniusQuotientEquiv_mk_pow (b : A) :
    perfectPrismVarpiFrobeniusQuotientEquiv W hW
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal b)) =
        Ideal.Quotient.mk (Ideal.span {(p : R)}) ((Ideal.Quotient.mk W.ideal b) ^ p) := by
  rw [perfectPrismVarpiFrobeniusQuotientEquiv_mk, (D).frobeniusLift_apply,
    map_add, map_pow, map_mul, map_natCast, map_add, map_mul]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : R)),
    zero_mul, add_zero]

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiFrobeniusQuotient

/-! ## 二元係数商から ϖ 商への逆 Frobenius

## 概要

完全 prism の係数二元商 A/(p,d) を R/ϖ と具体的に比較する。
BS 著者版 Remark 7.15（著者版 p.62）の係数作用を追う。

## 方針

既存の二重商と係数 Frobenius の二元イデアル比較を合成する。
逆方向が各係数に逆 Frobenius を適用することを計算する。

## 規約

prism 商の p 正則性や非零性を仮定しない。

## 使われ方

主 pd 表示の入力多項式がどの係数写像で移るかを明示する。
-/

@[expose] public noncomputable section PerfectPrismFrobeniusPairToVarpi

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "e" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "x" => perfectPrismVarpiLift W hW
local notation "K" => Ideal.span {(p : A), W.generator}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)

/-- 概要：ϖ 商から一重二元係数商への具体的 Frobenius 同型。
方針：二重商を一重商にし、Frobenius で (d,x) を (p,d) へ送る。
規約：元の係数作用を代表元で追える向きを選ぶ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆係数写像の構成。 -/
def perfectPrismVarpiToFrobeniusPairEquiv : Rv ≃+* A ⧸ K :=
  (principalDoubleQuotEquiv W.generator x).trans
    (Ideal.quotientEquiv _ _ e (perfectPrismVarpiFrobenius_pairIdeal W hW).symm)

/-- 概要：二元係数商への同型は代表元に Frobenius を適用する。
方針：二重商と標準商同型の代表元公式を使う。
規約：全ての r∈A を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式係数の移送。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_mk (r : A) :
    perfectPrismVarpiToFrobeniusPairEquiv W hW (barr r) = Ideal.Quotient.mk K (e r) := by
  rw [perfectPrismVarpiToFrobeniusPairEquiv, RingEquiv.trans_apply]
  change Ideal.quotientEquiv _ _ _ _
    (principalDoubleQuotEquiv W.generator x (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r))) = _
  rw [principalDoubleQuotEquiv_mk, Ideal.quotientEquiv_mk]

/-- 概要：逆係数同型は Frobenius 像の剰余を元の ϖ 剰余へ戻す。
方針：順写像の代表元公式と逆合成を使う。
規約：Frobenius は完全 δ 環の指定自己同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数作用の照合。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_symm_frobenius (r : A) :
    (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm (Ideal.Quotient.mk K (e r)) = barr r := by
  rw [← perfectPrismVarpiToFrobeniusPairEquiv_mk, RingEquiv.symm_apply_apply]

/-- 概要：逆係数同型は任意の代表元に逆 Frobenius を適用する。
方針：Frobenius の全射性と前公式を使う。
規約：係数を暗黙に同一視せず値を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力多項式の正確な比較。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_symm_mk (r : A) :
    (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm (Ideal.Quotient.mk K r) =
      barr ((e).symm r) := by
  have h := perfectPrismVarpiToFrobeniusPairEquiv_symm_frobenius W hW ((e).symm r)
  simpa only [RingEquiv.apply_symm_apply] using h

/-- 概要：逆 Frobenius による入力多項式の係数変更。
方針：全係数を完全 δ 環の逆 Frobenius で写す。
規約：この多項式を元の f と同一視しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主 pd 表示を ϖ 係数へ移す入力。 -/
def perfectPrismInverseFrobeniusPolynomial (f : Polynomial A) : Polynomial A :=
  f.map (e).symm.toRingHom

/-- 概要：逆 Frobenius で係数変更したモニック多項式もモニック。
方針：モニック性の環射による保存を使う。
規約：正次数は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の移送後の正則性と自由性。 -/
theorem perfectPrismInverseFrobeniusPolynomial_monic (f : Polynomial A) (hf : f.Monic) :
    (perfectPrismInverseFrobeniusPolynomial W hW f).Monic := hf.map _

end SerrePositivity.BhattScholze.Andre

end PerfectPrismFrobeniusPairToVarpi
