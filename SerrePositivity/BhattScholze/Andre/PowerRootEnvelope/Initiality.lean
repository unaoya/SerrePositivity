module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputCategory

/-!
# 向きなし入力圏での源の初期性と pd 包の普遍性

## 概要
原典係数上の分冪値、正次数モニック入力に対する源 prism の初期性と基底射を指定しない普遍性、固定完全基底上の向きなし入力圏とそこでの源の初期性、初期源と原典の係数計算の合流、ϖ 還元した無限根 pd 包の普遍性。
BS 著者版 Remark 7.15 の包の記述に向けて、向きなし入力圏での始性と φ 引き戻しに関わる分冪包の普遍性を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
BS の集約、`PowerRootEnvelope/Audit`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## 原典係数上の実分冪値と切断変数

## 概要

無限根モニック pd 包の p 冪次分冪は、切断表示の対応する変数へ写る。
BS 著者版 Remark 7.15(1)（著者版 p.62）の gᵢ の明示的な同定。

## 方針

無条件版の実分冪値の公式と、切断表示の標準生成元の公式を合わせる。
原典とは異なる射影的係数商からの分冪構造を使う。

## 規約

モニック性だけを要求し、prism 商の p 正則性と正次数を要求しない。

## 使われ方

旧 hpR 付き公開公式と同じ係数作用・切断表示・添字を保って置換する。
-/

@[expose] public noncomputable section PerfectPrismVarpiNativePDFormula

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" f => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr f)
local notation "Dv" f => PrincipalDPPresentation Nv (zv f)

/-- 概要：実 pd 包の素数冪分冪は切断表示の対応する変数へ写る。
方針：実分冪の標準値を使い、素数冪標準生成元の表示公式を適用する。
規約：g₁ を添字零の変数とし、次数は p^(i+1)。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の gᵢ と分冪値の具体的な対応。 -/
theorem perfectPrismVarpiNativePDEnvelope_truncated_dpow
    (f : Polynomial A) (hf : f.Monic)
    (i : ℕ) :
    let := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    perfectPrismVarpiNativePDEnvelope_truncatedEquiv W hW f
      ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow (p ^ (i + 1))
        (algebraMap Nv (Dv f) (zv f))) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  let := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
  rw [perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  change principalDPTruncatedEquiv p (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    (principalDPGenerator (zv f) (p ^ (i + 1))) = _
  exact principalDPTruncatedEquiv_generator_succ p
    (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f) i

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiNativePDFormula

/-! ## ϖ 還元した無限根実 pd 包の普遍性

## 概要

完全 prism 上のモニック入力について、ϖ の持上げによる無限根 pd 包の還元は、
その係数元を零にし入力元を分冪イデアルへ送る任意の標的への一意な分冪射を持つ。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数還元後の pd 普遍性。

## 方針

分冪包 の射影的係数商による実分冪構造と標準値の公式を使う。
原典の非零因子による帰着とは異なる射影的商の経路。
係数元の消滅から主イデアル全体を評価で殺し、商の普遍性を適用する。

## 規約

prism 商の p 正則性と正次数を要求しない。標的のねじれや完備性にも条件を課さない。

## 使われ方

係数変更後の台環の同型と組み合わせ、原典の R/ϖ 上の pd 包と比較する。
-/

@[expose] public noncomputable section PerfectPrismVarpiPDUniversalUnconditional

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "N" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "z" f => powerRootCoefficientPDInput p f

/-- 概要：ϖ の持上げで還元した実 pd 包から分冪標的への射は一意に存在する（BS 著者版 Remark 7.15 の証明中の PD 比較でモニック根の包の普遍性）。
方針：標的の係数消滅条件を主イデアル全体へ拡張し、商の実 pd 普遍性を使う。
原典とは異なる射影的係数商からの分冪構造を使う。
規約：係数射は無限根環 N からの指定代数構造。正次数仮定は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の R/ϖ 係数上の実 pd 包の比較。 -/
theorem existsUnique_perfectPrismVarpiPDMorphism_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra N B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap N B (z f) ∈ I)
    (haB : algebraMap N B (algebraMap R₀ N
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))) = 0) :
    ∃! F : ((D f) ⧸ Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))}) →ₐ[N] B,
      (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf).IsDPMorphism Ht F.toRingHom := by
  let a := Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
  let K : Ideal (D f) := Ideal.span {algebraMap R₀ (D f) a}
  have hcoeff : principalDPEval Ht (z f) hzB (algebraMap R₀ (D f) a) = 0 := by
    rw [IsScalarTower.algebraMap_apply R₀ N (D f), AlgHom.commutes]
    exact haB
  have hK : ∀ t ∈ K, principalDPEval Ht (z f) hzB t = 0 := by
    have hle : K ≤ RingHom.ker (principalDPEval Ht (z f) hzB).toRingHom := by
      apply Ideal.span_le.mpr
      intro t ht
      have ht' : t = algebraMap R₀ (D f) a := Set.mem_singleton_iff.mp ht
      subst t
      exact hcoeff
    exact fun t ht => hle ht
  exact existsUnique_principalDPQuotientMorphism (z f) K Ht hzB hK
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
    (perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional W hW f hf)

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiPDUniversalUnconditional

/-! ## André ϖ 還元した PD 包の普遍性の移行

## 概要

BS 著者版 Remark 7.15(1)（著者版 p.62）の元の係数消滅条件を持つ普遍性を無条件版へ移す。

## 方針

射影的係数商からの分冪構造を使い、旧主張から hpR だけを除く。原典とは異なる経路。

## 規約

不要になった旧 hpR 付き公開名を削除し、`existsUnique_perfectPrismVarpiPDMorphism_of_unconditional`
をこの import 経路で公開する。正次数は追加しない。

## 使われ方

同じ標準商・係数消滅条件で原典の PD 包の普遍性を適用する。
-/

/-! ## André 正次数モニック入力に対する元の源 prism の初期性

## 概要

元の H の prism 性と原典の完備入力作用を持つ有界 prism 圏での初期性を証明する。
BS 著者版 Remark 7.15（著者版 p.62）の源の構成と普遍性の合流。

## 方針

分冪包 の元の H の生成元正則性と同じ T の有界性を、既存の条件付き初期性へ渡す。
原典を補う実逐次完備化・純性・明示的な入力圏による経路。

## 規約

完全 prism と正次数モニック入力だけを仮定し、hpR・hreg・hBound は引数に残さない。
固定完全基底と向き付き prism の圏での初期性を扱う。絶対 site 全体との比較は別工程。

## 使われ方

原典の完備入力環 S の作用を持つ元の源と、同じ圏の任意の envelope の比較に使う。
-/

@[expose] public noncomputable section PowerRootPrismMonicSourceInitiality

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

open _root_.CategoryTheory _root_.CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

set_option maxHeartbeats 800000 in
-- 元の H の環構造と 分冪包 の生成元正則性の依存型を照合するため。
/-- 概要：正次数モニック入力から元の H に prism 構造を与える。
方針：分冪包 の同じ標準分母像の正則性を既存の prism 構成へ渡す。
規約：prism 商の p 正則性や源の正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の prismatic 源。 -/
def powerRootPrismMonicCompletionPrismOfMonicPositive :
    let := pdCompletionCommRing L p (jL dP)
    OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicCompletionPrismOfRegular W hW f
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 元の H の prism 構造の生成元を定義と照合するため。
/-- 概要：正次数モニック源 prism の生成元は元の標準分母像。
方針：正則性から作った prism の計算規則を使う。
規約：同じ H と同じ生成元を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H/dH の同定。 -/
theorem powerRootPrismMonicCompletionPrismOfMonicPositive_generator :
    let := pdCompletionCommRing L p (jL dP)
    (powerRootPrismMonicCompletionPrismOfMonicPositive W hW f hf hdeg).generator =
      uL (jL dP) := by
  rfl

set_option maxHeartbeats 800000 in
-- 完備入力の係数作用と元の H の正則性・有界性を一つの対象で照合するため。
/-- 概要：正次数モニック入力から元の H を有界入力 prism の対象とする。
方針：分冪包 の生成元正則性と同じ通常商 T の有界性を既存の構成へ渡す。
規約：hpR・hreg・hBound を引数に残さず、原典の順序の完備入力環を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準源の初期性。 -/
def powerRootPrismMonicSourceInputObjectOfMonicPositive : BoundedPrismInput W cS := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceInputObject W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 元の H の依存する入力対象と既存の初期性の型を照合するため。
/-- 概要：元の正次数モニック源は有界入力 prism の圏で初期。
方針：分冪包 の同じ H と T の結果により初期性の二つの補助仮定を解消する。
規約：固定完全基底・向き付き対象の圏での結果であり、絶対 site 比較は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の envelope 比較の合流点。 -/
def powerRootPrismMonicSourceInput_isInitialOfMonicPositive :
    IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg) := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceInput_isInitial W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 同じ H の台環と入力圏の任意の初期対象との比較を保つため。
/-- 概要：同じ入力圏の任意の初期対象と元の正次数モニック源 H は環同型。
方針：補助仮定を 分冪包 から供給して既存の初期対象比較を適用する。
規約：比較先の初期性だけはその普遍性として明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の同じ圏での envelope の一意性。 -/
def powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) :
    let := pdCompletionCommRing L p (jL dP)
    H ≃+* Z.ring := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceEnvelopeRingEquiv W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg) Z hZ

set_option maxHeartbeats 800000 in
-- 同型の基底保存性を元の H の全係数像の公式として照合するため。
/-- 概要：正次数モニック源と任意の初期対象の環同型は元の A の係数像を保つ。
方針：既存の基底保存公式に 分冪包 の正則性・有界性を代入する。
規約：元の標準係数射を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典との係数作用の比較。 -/
theorem powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive W hW f hf hdeg Z hZ
      (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base.toRingHom a₀ := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceEnvelopeRingEquiv_base_coeff W hW f hf a₀
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg) Z hZ

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicSourceInitiality

/-! ## André 基底射を指定しない有界入力への源の普遍性

## 概要

元の正次数モニック源は、完備入力作用だけを持つ任意の有界な向き付き prism へ一意に写る。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope の普遍性の向き付き対象での形。

## 方針

入力作用の係数制限から、BS 著者版 Lemma 4.8（著者版 pp.38–39）の証明済みの持上げで基底射を作る。
固定基底上での源の普遍性を適用し、完全基底からの剛性で任意の入力保存射の基底保存性を回復する。
原典の変形理論とは異なる tilt 比較・Fontaine 写像・実完備化による経路。

## 規約

標的の完全性・p 正則性や基底射の選択は引数に残さない。源の hreg・hBound も要求しない。
向き付き prism を扱い、一般 Cartier イデアルを持つ対象との比較は別工程。

## 使われ方

原典の順序の完備入力環 S の作用だけを与えた場合の、同じ H の初期性の判定。
-/

@[expose] public noncomputable section PowerRootPrismMonicAbsoluteUniversal

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable {B : Type u} [CommRing B]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

open _root_.CategoryTheory _root_.CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

set_option maxHeartbeats 800000 in
-- 元の H の環構造・標準入力・持上げた基底射を同時に照合するため。
/-- 概要：完備入力作用だけを持つ任意の有界 prism への源からの射は一意に存在。
方針：完全基底の商射を一意に持ち上げ、固定基底の普遍性と基底射の剛性を使う。
規約：源の正則性・有界性、標的の基底射を仮定に残さず、入力圏と同じ宇宙で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope の向き付き対象での普遍性。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_of_absolute_input
    (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal) :
    let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
    ∃! G : OrientedPrism.Hom X.prism Q, G.quotientMap.comp X.input = η := by
  let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
  obtain ⟨k, hk, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded W hW Q hB (η.comp cS)
  let := pdCompletionCommRing L p (jL dP)
  have hreg := powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional
    W hW f hf hdeg
  have hBound := powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional
    W hW f hf hdeg
  obtain ⟨G, hG, hu⟩ := existsUnique_powerRootPrismMonicPrismHom_of_bounded_source
    W hW f Q k hf hB η hk.symm hreg hBound
  refine ⟨G, hG.2, ?_⟩
  intro G' hG'
  have hb : G'.comp X.base = k := by
    apply _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target W hW Q hB
    rw [OrientedPrism.Hom.quotientMap_comp, ← X.input_base,
      ← RingHom.comp_assoc, hG', hk]
  exact hu G' ⟨hb, hG'⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicAbsoluteUniversal

/-! ## 向きなし入力圏での元の源の初期性

## 概要
向き付き入力の源 の正次数モニック源の初期性を向きなし入力圏へ移す。
## 方針
圏同値の恒等環射による比較同型と、既存の初期性を使う。
## 規約
固定完全基底と同じ宇宙の対象に限る。元の H と完備入力の作用を変更しない。
## 使われ方
BS 著者版 Remark 7.15（著者版 p.62）の向きに依存しない普遍性を公開する。
-/

@[expose] public noncomputable section Initial

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable {W : OrientedPrism p A} {c : A ⧸ W.ideal →+* S}

/-- 概要：向き付き入力対象の初期性は向きなし対象へ移る。
方針：同値の比較同型で源を移し、射の一意性をそのまま使う。
規約：任意の入力対象に適用でき、完全性は固定基底だけに要求する。
使われ方：元の源の向きなし初期性への共通接続。 -/
def BoundedPrismInput.initial_unoriented (hW : W.deltaStructure.IsPerfect)
    (X : BoundedPrismInput W c) (hX : IsInitial X) :
    IsInitial (BoundedPrismInputUnoriented.forget X) := by
  have hi := hX.ofIso (BoundedPrismInputUnoriented.orientationIso X).symm
  apply IsInitial.ofUniqueHom (fun Y => hi.to (BoundedPrismInputUnoriented.orient Y))
  intro Y f
  exact hi.hom_ext _ _

/-- 概要：元の正次数モニック源は向きなし有界入力 prism の圏で初期。
方針：向き付き入力の源 の証明済みの初期性を、向きを忘れる関手に沿って移す。
規約：正則性・有界性の追加仮定はなく、元の台環・δ・基底・入力を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の固定完全基底での向きなし envelope。 -/
def powerRootPrismMonicSourceInput_initial_unoriented
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsInitial (BoundedPrismInputUnoriented.forget
      (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)) :=
  BoundedPrismInput.initial_unoriented hW _
    (powerRootPrismMonicSourceInput_isInitialOfMonicPositive W hW f hf hdeg)

end SerrePositivity.BhattScholze.Andre

end Initial

/-! ## 元の André 源の向きなし入力圏での初期性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の源 H の初期性を固定完全基底上の向きなし入力圏へ移す。

## 方針
向き付き入力圏との証明済みの同値に初期性を沿わせる。

## 規約
元の正次数モニック性だけを引き継ぎ、hpR・正則性・有界性を追加しない。

## 使われ方
向きなしの任意の初期対象と元の H の比較に使う。
-/

@[expose] public noncomputable section SourceInitiality

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "R" => A ⧸ W.ideal

local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)

open _root_.CategoryTheory _root_.CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

/-- 概要：元の正次数モニック源を向きなし入力対象とする。
方針：既存の源に忘却関手を適用する。
規約：台環・δ 構造・基底・入力作用を保持する。
使われ方：BS 著者版 Remark 7.15（p.62）の向きなしの標準源。 -/
def powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented :
    BoundedPrismInputUnoriented W cS :=
  (BoundedPrismInputUnoriented.forgetFunctor (W := W) (c := cS)).obj
    (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)

/-- 概要：元の正次数モニック源は向きなし入力圏で初期。
方針：圏同値による初期性の保存を使う。
規約：既存の hdeg を保持し、追加条件を置かない。
使われ方：BS 著者版 Remark 7.15（p.62）の固定基底上の向きなし普遍性。 -/
def powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented :
    IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg) :=
  powerRootPrismMonicSourceInput_initial_unoriented W hW f hf hdeg

/-- 概要：向きなし入力圏の任意の初期対象と元の H は環同型。
方針：初期対象の一意な同型を標準 orientation 関手で実環の同型へ戻す。
規約：比較先にはその初期性だけを要求する。
使われ方：BS 著者版 Remark 7.15（p.62）の向きなし envelope の一意性。 -/
def powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented
    (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) :
    let := pdCompletionCommRing L p (jL dP)
    H ≃+* Z.ring := by
  let := pdCompletionCommRing L p (jL dP)
  exact BoundedPrismInput.isoRingEquiv
    (BoundedPrismInputUnoriented.orientFunctor.mapIso
      ((powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented
        W hW f hf hdeg).uniqueUpToIso hZ))

/-- 概要：向きなし初期対象との環同型は全ての基底係数像を保つ。
方針：比較同型の射の基底保存等式を各元に適用する。
規約：元の標準係数射と比較先の基底環射を保持する。
使われ方：BS 著者版 Remark 7.15（p.62）の入力作用の照合。 -/
theorem powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff_unoriented
    (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented W hW f hf hdeg Z hZ
      (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base a₀ := by
  let := pdCompletionCommRing L p (jL dP)
  let e := (powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented
    W hW f hf hdeg).uniqueUpToIso hZ
  exact RingHom.congr_fun (congrArg OrientedPrism.Hom.toRingHom e.hom.over_base) a₀

/-- 概要：向きなし標的の任意の完備入力作用を保つ源からの prism 射は一意に存在。
方針：標的の基底生成元像による標準 orientation と商同型を既存の絶対普遍性へ渡す。
規約：η に標的の既存基底射との可換性を要求せず、基底保存条件を結論に追加しない。
使われ方：BS 著者版 Remark 7.15（p.62）の基底射を指定しない入力作用の普遍性。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented
    (Q : BoundedPrismInputUnoriented W cS) (η : SI →+* Q.ring ⧸ Q.ideal) :
    let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
    ∃! G : OrientedPrism.Hom X.prism Q.orient.prism,
      G.quotientMap.comp X.input = (Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η :=
  existsUnique_powerRootPrismMonicPrismHom_of_absolute_input W hW f hf hdeg
    Q.orient.prism Q.orient.bounded ((Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η)

end SerrePositivity.BhattScholze.Andre

end SourceInitiality

/-! ## André：固定完全基底上の向きなし入力圏

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の向きなし入力圏と元の源の初期性を集約する。

## 方針
基底生成元像による標準 orientation と既存の向き付き入力圏の同値を用いる。

## 規約
主定理と引用件数は変更しない。基底を動かす一般化は含まない。

## 使われ方
向きなしの有界試験対象と André 源の普遍性の照合の入口。
-/

/-! ## 元の初期源と原典の係数計算の合流

## 概要

完全 prism 上の正次数モニック入力について、元の源の向きなし初期性と、
自然な Hodge–Tate 商の p 完全忠実平坦性・ϖ 剰余の pd 表示と自由性を同時に得る。
BS 著者版 Remark 7.15(1)（著者版 p.62）の同じ源の係数計算。

## 方針

向き付き入力の源・向きなし入力の源 の初期性、分冪包 の実源の純性、係数比較 の自然な係数比較を合流する。
通常剰余からの逆向きには元の源の証明済み完全忠実平坦性を使う。
原典の p ねじれなしへの帰着とは異なる純性・圏同値による経路。

## 規約

hpR・正則性・有界性を追加仮定に残さない。元の H と標準係数作用を保持する。
ϖ 剰余の入力は逆 Frobenius 係数変更 f' であり、元の f と同一視しない。
向きなし初期性は固定完全基底上の J=(d)B を満たす入力圏について述べる。

## 使われ方

原典の prismatic 源の普遍性と係数の自由性を同じ実対象について参照する公開入口。
-/

@[expose] public noncomputable section PowerRootPrismMonicCoefficientComparison

namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
open _root_.SerrePositivity.BhattScholze.Andre.VarpiComparison
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Rv" => R ⧸ Ideal.span {v}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f
local notation "Tv" => T ⧸ Ideal.map φ (Ideal.span {v})
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {v})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map barr (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Qv" => Nv ⧸ Ideal.span {zv ^ p}
local notation "hpv" => perfectPrismVarpiRootRing_prime_eq_zero W hW


/-- 概要：元の向きなし初期源について、同じ商の pd 係数比較と忠実平坦性が成立する。
方針：既存の初期性の実証人と無条件な候補比較を同じ H のまま合流する。
規約：固定基底上の入力圏と正次数モニック性を保持し、追加仮定を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の初期源と係数計算の一括参照。 -/
theorem powerRootPrismMonicSource_initial_and_coefficient_comparison
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    let := varpiCoefficientAlgebra W hW
    Nonempty (CategoryTheory.Limits.IsInitial
      (powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg)) ∧
      (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
      Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv) := by
  exact ⟨⟨powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented W hW f hf hdeg⟩,
    hodgeTate_coefficient_comparison_of_unconditional W hW f hf hdeg⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCoefficientComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 7.15" (partial := special) "主張（R→S が mod p で ind-syntomic な被覆）は証明していない。使っているのは構成の部分：S=R⟨Y^{1/p^∞}⟩/(f(Y)) の prismatic envelope T と φ^*(T/ϖ) の pd 包の記述、cover 性（完全忠実平坦）で、これが Thm 7.14 の一段拡大になる。docstring の「BS Rem 7.15」引用（1,700 件超）はこの計算を指す ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：exists_monicRootPerfectoidExtension（Andre/Transfinite/Tower.lean:1172。型は R からの一段拡大の存在。原文が直接扱う方程式商 S から T への被覆や mod p ind-syntomic ） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Andre.existsUnique_perfectPrismVarpiPDMorphism_of_unconditional
