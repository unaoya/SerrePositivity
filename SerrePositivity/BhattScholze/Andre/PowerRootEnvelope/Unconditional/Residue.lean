module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.BhattScholze.Andre.Envelope.JetKoszul
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Localization
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionResidue
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# 追加の正則性を仮定しない残余比較

## 概要
無限根初期係数商と通常モニック商、prism 商の p 正則性を使わないモニック pd 包、R/ϖ の標数条件、残余 Koszul 分解と導来評価比較、係数還元、A 係数での (p,d) 還元、raw 残余商と H⁰ の忠実平坦性、raw 包の最初の段の p 正則性、ϖ の持ち上げによる hpR の解消。
BS 著者版 Remark 7.15 の包に関わる剰余比較を、追加の正則性を置かずに与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Audit`、`PowerRootEnvelope/Initiality`、`PowerRootEnvelope/Unconditional/FrobeniusPD`、`PowerRootEnvelope/Unconditional/Source`、`PowerRootEnvelope/VarpiComparison`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## prism 商の p 正則性を使わないモニック pd 包

## 概要

完全 prism 上のモニック入力について、R/ϖ と R/p の無限根標準表示に
実分冪構造・入力分冪公式・pd 普遍性を与える。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数還元における追加正則性を解消する。

## 方針

正次数商の自由性から任意係数元による分冪降下を使い、ϖ の持上げで還元する。
原典とは異なる線形切断・実環同型・分冪構造の移送による証明。

## 規約

完全 prism と入力のモニック性のみを使い、prism 商の p 正則性・正次数を仮定しない。
二つの係数環を明示し、mod p 側の入力は元の f の係数像とする。

## 使われ方

A 全体の実 Frobenius 引戻しに、追加正則性なしの実分冪構造と pd 普遍性を供給する。
-/

@[expose] public noncomputable section MonicPDEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
section Native
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "N" => PowerRootPolynomial R₀ p hp
local notation "z" => powerRootCoefficientPDInput p f
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "a" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "K" => Ideal.span {algebraMap R₀ D a}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：原典の係数環上のモニック入力の標準表示に実分冪構造を与える。
方針：射影的な正次数商により還元した構造を表示環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def perfectPrismVarpiNativeDividedPowers_of_unconditional
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zv) :=
  DividedPowers.ofRingEquiv (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (powerRootCoefficientPDReductionOfMonic p W hW f hf a)

/-- 概要：原典の係数環上でも入力元の分冪は全標準生成元に一致する。
方針：移送公式と還元前の標準値の公式、同型の入力・生成元の比較を使う。
規約：全次数 n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 普遍性への入力。 -/
theorem perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional
    (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow n
      (algebraMap Nv Dv zv) = principalDPGenerator zv n := by
  rw [← perfectPrismVarpiPDEnvelopeEquiv_input W hW f,
    perfectPrismVarpiNativeDividedPowers_of_unconditional, DividedPowers.ofRingEquiv_dpow_apply,
    powerRootCoefficientPDReductionOfMonic_base_apply,
    perfectPrismVarpiPDEnvelopeEquiv_generator]

/-- 概要：原典の係数環上の実 pd 包から任意の分冪標的への射は一意に存在する。
方針：移送済みの実分冪構造と標準値を一般の pd 普遍性へ供給する。
規約：標的は無限根環 Nv の任意の代数。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の実 pd 包の同定。 -/
theorem existsUnique_perfectPrismVarpiNativePDMorphism_of_unconditional
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
    ∃! F : Dv →ₐ[Nv] B,
      (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).IsDPMorphism
        Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zv
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)
    (perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional W hW f hf) Ht hzB

end Native

section Prime
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => (A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ W.ideal)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW

variable (f : Polynomial A)
local notation "zv" => powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map bv (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Dp" => PrincipalDPPresentation Np zp

local notation "fInv" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "hMonicInv" => perfectPrismInverseFrobeniusPolynomial_monic W hW f
local notation "rootEq" => powerRootVarpiPrimeFrobeniusEquiv W hW
local notation "hInput" => powerRootVarpiPrimeFrobeniusEquiv_input W hW f

/-- 概要：元の mod p 入力の標準表示は実分冪構造を持つ。
方針：逆係数入力の実分冪構造を入力を保つ係数環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の同定。 -/
def powerRootPrimeFrobeniusDividedPowers_of_unconditional
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zp) :=
  principalDPTransportDividedPowers rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW fInv (hMonicInv hf))

/-- 概要：元の入力の n 次分冪は n 次標準生成元。
方針：入力を保つ係数移送の分冪公式と元の標準値を使う。
規約：零次数を含む全次数を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 普遍性の入力。 -/
theorem powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional
    (hf : f.Monic) (n : ℕ) :
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf).dpow n
      (algebraMap Np Dp zp) = principalDPGenerator zp n :=
  principalDPTransportDividedPowers_base_apply rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW fInv (hMonicInv hf))
    (perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional W hW fInv (hMonicInv hf)) n

/-- 概要：元の mod p 入力の実分冪包から任意の分冪標的への射は一意に存在。
方針：標準分冪値を持つ一次関係商の一般普遍性を適用する。
規約：標的は Np の任意の代数と分冪イデアル。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実テンソル比較先の pd 包性。 -/
theorem existsUnique_powerRootPrimeFrobeniusPDMorphism_of_unconditional
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    ∃! F : Dp →ₐ[Np] B,
      (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf).IsDPMorphism
        Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zp
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) Ht hzB

end Prime
end SerrePositivity.BhattScholze.Andre

end MonicPDEnvelope

/-! ## ϖ 持上げによる分冪還元の hpR 解消

## 概要
BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力について、prism 商の p 正則性なしに分冪を降下する。

## 方針
コミット 4c97d497 の射影的正次数商の線形切断を使い、元の還元環と元の入力を保つ。

## 使われ方
既存 PerfectPrismVarpiRegular の三つの分冪宣言を置換するための別名の受渡し。
-/

@[expose] public noncomputable section VarpiPDReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "z" f => powerRootCoefficientPDInput p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：原典の ϖ の持上げで還元した無限根 pd 包に実分冪構造を与える。
方針：モニック正次数商の射影性により任意係数元の降下を適用する。
規約：f のモニック性のみを仮定し、prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ への係数変更。 -/
def perfectPrismVarpiPowerRootDividedPowers_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers ((J f).map
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))}))) :=
  powerRootCoefficientPDReductionOfMonic p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))

/-- 概要：ϖ 還元後の入力元の分冪は標準分冪生成元の商像。
方針：一般射影的係数還元の計算公式を具体的な持上げに適用する。
規約：全次数を含み、還元前と同じ入力元を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 普遍射の照合。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf).dpow n
      (Ideal.Quotient.mk _ (algebraMap
        (PowerRootPolynomial R₀ p (Nat.Prime.pos (Fact.out : p.Prime))) (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  unfold perfectPrismVarpiPowerRootDividedPowers_of_unconditional
  exact powerRootCoefficientPDReductionOfMonic_base_apply p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) n

/-- 概要：ϖ の持上げによる商への標準射は分冪を保つ。
方針：一般射影的係数還元の分冪射の定理を使う。
規約：分冪イデアルは正次数イデアルの実商像。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数還元の構造射。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))})) := by
  unfold perfectPrismVarpiPowerRootDividedPowers_of_unconditional
  exact powerRootCoefficientPDReductionOfMonic_isDPMorphism p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))

end SerrePositivity.BhattScholze.Andre

end VarpiPDReduction

/-! ## hpR を使わない無限根モニック入力の実残余 Koszul 分解

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の raw 包について、mod(p,d) の有限 δ 関係列は
hpR なしに Koszul 分解を与える。

## 方針
初項は負のモニック入力であり、係数二元商上で正則。
以後は既存の distinguished 係数と Witt 計算による残余正則列を使う。

## 規約
mod p の d の正則性や raw 環の p 正則性を仮定しない。

## 使われ方
正則対の経路を使わず、元の完備化の実導来剰余を計算するための入力。
-/

@[expose] public noncomputable section PowerRootResidueKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "KP" => Ideal.span {(p : P), dP}
local notation "K" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "q" => Ideal.Quotient.mk K

include hf in
/-- 概要：最初の実 δ 関係は mod(p,d) の自由環で正則。
方針：係数商との交換で負のモニック入力へ移し、多項式の平坦性を用いる。
規約：d mod p の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の hpR なしの有限残余帰納法の初項。 -/
theorem powerRootPrismMonicFirst_mod_pair_regular_of_unconditional :
    IsSMulRegular (L₀ ⧸ K) (q (deltaDivisionIteratedRelation E dP a default 0)) := by
  have hK : (KP).map (MvPolynomial.C : P →+* L₀) = K := by
    rw [Ideal.map_span, Set.image_pair, map_natCast]
  let e := (Ideal.quotEquivOfEq hK.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := PUnit.{u + 1} × ℕ) KP).symm.toRingEquiv
  have he (x : L₀) : e (q x) = MvPolynomial.map (Ideal.Quotient.mk KP) x := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp
      (PUnit.{u + 1} × ℕ) P KP) x
  have hd : Ideal.Quotient.mk KP dP = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [he]
  change IsSMulRegular _ (MvPolynomial.map (Ideal.Quotient.mk KP)
    (MvPolynomial.C dP * MvPolynomial.X (default, 0) -
      MvPolynomial.C (powerRootMonicPDInput p f)))
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.map_C, hd, map_zero, zero_mul, zero_sub]
  have hr := powerRootPolynomial_monic_mod_pair_regular p hp W.generator f hf
  have hl := hr.of_flat (S := MvPolynomial (PUnit.{u + 1} × ℕ) (P ⧸ KP))
  intro x y hxy
  apply hl
  simpa only [smul_eq_mul, neg_mul, neg_inj, MvPolynomial.algebraMap_eq,
    powerRootMonicPDInput] using hxy

include hf in
/-- 概要：元の有限 δ 関係列は mod(p,d) で全深さにおいて弱正則。
方針：モニック初項、完全 prism の p 正則性、自由環の ghost 単射性を一般残余定理へ渡す。
規約：hpR や正次数を追加せず、元の全有限関係を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無条件の実導来還元の Tor 消滅。 -/
theorem powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ K)
      (List.ofFn fun i : Fin (N + 1) =>
        q (deltaDivisionIteratedRelation E dP a default i.val)) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)
  let hd := powerRootPrismGenerator_isDistinguished W hW
  exact deltaDivisionFiniteResidueRelations_isWeaklyRegular E dP a hpP hpL
    (witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL) hd.unit hd.unit_spec
    (powerRootPrismMonicFirst_mod_pair_regular_of_unconditional W hW f hf) N

include hf in
/-- 概要：元の有限 δ 関係列は mod(p,d) で Koszul 分解。
方針：既証の弱正則列の分解判定を適用する。
規約：hpR と正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実剰余 Tor 計算。 -/
theorem powerRootPrismMonicFiniteResidue_isKoszulResolution_of_unconditional (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q (deltaDivisionIteratedRelation E dP a default i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional W hW f hf N)

include hf in
/-- 概要：実評価関係の全有限深さの残余 Koszul 複体も分解を与える。
方針：δ 反復列と実評価列の三角比較を用いる。
規約：元の係数商・実関係を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全評価源への Tor 移送。 -/
theorem powerRootPrismMonicFiniteResidueEvaluation_isKoszulResolution_of_unconditional
    (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q (deltaDivisionEvaluationRelation E dP a default i.val)) :=
  deltaDivisionMappedEvaluation_isKoszulResolution E dP a q
    (fun N => powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional W hW f hf N) N

local notation "ψ" => RingHom.comp q (deltaDivisionSourceMap E dP)

include hf in
/-- 概要：実残余自由 δ 射に沿う一つの有限源商の正次数 Tor は零。
方針：源グラフの Koszul 分解で実評価関係のホモロジーへ移す。
規約：δ 深さと正次数のすべてを扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無条件の実導来剰余比較の有限入力。 -/
theorem powerRootPrismMonicFiniteResidueSource_tor_subsingleton_of_unconditional
    (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1)
      (DeltaDivisionEvaluationSourceFiniteQuotient E a N)) := by
  let cs : Fin (N + 1) → PUnit.{u + 1} × ℕ := fun j => (default, j.val)
  have hcs : Function.Injective cs := by
    intro x y hxy
    exact Fin.ext (congrArg Prod.snd hxy)
  have e := SerrePositivity.torAlgKoszulIso ψ
    (fun j => deltaDivisionSourceGraphRelation E a (cs j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E a cs hcs) (i + 1)
  have he : ψ ∘ (fun j => deltaDivisionSourceGraphRelation E a (cs j)) =
      (fun j : Fin (N + 1) => q (deltaDivisionEvaluationRelation E dP a default j.val)) := by
    funext j
    exact congrArg q (deltaDivisionSourceGraph_map E dP a (cs j))
  rw [he] at e
  have hr := powerRootPrismMonicFiniteResidueEvaluation_isKoszulResolution_of_unconditional
    W hW f hf N
  exact ModuleCat.subsingleton_of_isZero
    ((hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)).of_iso e)

include hf in
/-- 概要：元の全評価源の、実残余自由 δ 射に沿う正次数 Tor は零。
方針：有限深さの消滅を、証明済みの Tor と逐次余極限の交換で全評価環へ渡す。
規約：hpR や新しい交換仮定を残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無条件の標準導来 augmentation の入力。 -/
theorem powerRootPrismMonicResidueSource_tor_subsingleton_of_unconditional (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E a
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E a
  let := SerrePositivity.torAlg_preservesSequentialColimits ψ (i + 1)
  exact deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit E a ψ i
    (fun N => powerRootPrismMonicFiniteResidueSource_tor_subsingleton_of_unconditional
      W hW f hf N i) inferInstance

end SerrePositivity.BhattScholze.Andre

end PowerRootResidueKoszul

/-! ## 元の無限根モニック残余源の無条件の導来評価比較

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実残余自由 δ 源の導来評価は、
元の raw (p,d) 剰余の single 対象に一致する。

## 方針
全有限 δ 深さの Koszul 分解と Tor の逐次余極限保存から全評価源の Tor 消滅を得る。
Tor の対称性と標準 augmentation を用い、通常の残余 tensor を同定する。

## 規約
hpR と正次数は不要であり、ねじれ除去商へ置き換えない。

## 使われ方
元の実完備化の hpR なしの導来剰余計算へ渡す。
-/

@[expose] public noncomputable section PowerRootResidueSource

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₁" => PowerRootPolynomial A p hp
local notation "E₁" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A P₁ d
local notation "c₁" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₁" => PowerRootUnaryFreeDeltaRing A p hp
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C dP}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁) (deltaDivisionSourceMap E₁ dP)
local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁
local notation "Mβ" => baseChangeScalarModule β₁

set_option maxHeartbeats 800000 in
-- 無限根環と自由 δ 環に沿う二つの制限係数構造を Tor 比較で照合するため。
include hf in
/-- 概要：Tor対称性で、同じ実残余終域をβに沿って導来拡大するための消滅条件を得る。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：元の一元入力を固定し、hpR と正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem powerRootPrismMonicResidueSourceEval_torVanishing_of_unconditional :
    scalarExtensionTorVanishing β₁ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
      let : Subsingleton (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        powerRootPrismMonicResidueSource_tor_subsingleton_of_unconditional W hW f hf i
      have hz : IsZero (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₁ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₁).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₁ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT


local notation "Q₁" => L₁ ⧸ K₁
local notation "Res₁" => DeltaAdjoinDivisionResidue E₁ dP c₁

include hf in
/-- 概要：無限根モニック入力の実残余終域の導来評価は raw (p,d) 商の次数零対象と標準同型。
方針：高次 Tor 消滅による標準 augmentation と、通常残余テンソルの既存同型を合成する。
規約：同じ元の自由 δ 源射と評価射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
def powerRootPrismMonicResidueSourceDerivedIso_of_unconditional :
    (boundedAboveDerivedBaseChange β₁).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₁ Res₁) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := PUnit.{u + 1}) E₁ dP
  letI : Module L₁ Q₁ := Algebra.toModule
  let e₁ : ((ModuleCat.extendScalars β₁).obj Mψ) ≃ₗ[P₁] (P₁ ⊗[L₁] Q₁) :=
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := e₁.trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₁ dP c₁).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₁ Mψ
    (powerRootPrismMonicResidueSourceEval_torVanishing_of_unconditional W hW f hf) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

end SerrePositivity.BhattScholze.Andre

end PowerRootResidueSource

/-! ## 元の無限根入力の実係数還元の無条件比較

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の自由 δ 源上の実導来還元を、同じ raw 残余商へ比較する。

## 方針
hpR なしの実導来評価比較と、商射の全射性による係数作用の降下を用いる。

## 規約
モニック性のみを保持し、元の自由環・raw 商を変更しない。

## 使われ方
元の A 上への係数制限と実逐次完備化の hpR 解消へ渡す。
-/

@[expose] public noncomputable section PowerRootCoefficientReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P₀ W.generator
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ dP c₀
local notation "r₀" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E₀ dP c₀)

/-- 概要：一般モニック f/d 包の自由 δ 源上の三因子導来還元対象。
方針：評価・除算の二因子導来テンソルを実 (p,d) 商のスカラー対象とテンソルする。
規約：導来還元の実対象を明示する。平坦性は定義に含めない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商還元を raw 剰余へ比較する。 -/
abbrev PowerRootPrismMonicSourceCoefficientReduced_of_unconditional :=
  boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject q₀)

/-- 概要：無限根モニック入力について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional (hf : f.Monic) :
    PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ dP c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (powerRootPrismMonicResidueSourceDerivedIso_of_unconditional W hW f hf)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 概要：実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def powerRootPrismMonicSourceCoefficientResidueHomologyZeroIso_of_unconditional (hf : f.Monic) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional W hW f hf))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 概要：実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
theorem powerRootPrismMonicSourceCoefficientResidue_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional W hW f hf)))


end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientReduction

/-! ## 元の無限根入力の実係数還元の無条件比較

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の自由 δ 源上の実導来還元を、同じ raw 残余商へ比較する。

## 方針
hpR なしの実導来評価比較と、商射の全射性による係数作用の降下を用いる。

## 規約
モニック性のみを保持し、元の自由環・raw 商を変更しない。

## 使われ方
元の A 上への係数制限と実逐次完備化の hpR 解消へ渡す。
-/

@[expose] public noncomputable section PowerRootQuotientDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P₀ W.generator
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ dP c₀
local notation "r₀" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E₀ dP c₀)

/-- 概要：実二因子導来テンソルを実商環Q上へ基底変更した対象。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
abbrev PowerRootPrismMonicSourceQuotientDerived_of_unconditional :=
  (boundedAboveDerivedBaseChange q₀).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα))

/-- 概要：raw残余商上のβを経由する源作用の、実商環への標準降下。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientResidueMap_of_unconditional : Q₀ →+* Res₀ :=
  Ideal.Quotient.lift K₀ ((r₀).comp ((j₀).comp β₀)) (by
    change K₀ ≤ RingHom.ker ((r₀).comp ((j₀).comp β₀))
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change r₀ ((j₀).comp β₀ (p : L₀)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert _ _))
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      change r₀ (j₀ (β₀ (MvPolynomial.C dP))) = 0
      rw [deltaDivisionSourceEval_C]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- 概要：商代表元の作用は、β、raw係数射、残余商射の合成である。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientResidueMap_mk_of_unconditional (x : L₀) :
    powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f (q₀ x) =
      r₀ (j₀ (β₀ x)) := rfl

/-- 概要：商環作用をqで制限すると、前工程のβによる実L加群になる。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientResidueRestrictionIso_of_unconditional :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Res₀)) ≅ MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact
    { hom := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change r₀ (j₀ (β₀ r)) * x = (β₀ r) • x
            rw [Algebra.smul_def]
            rfl } }
      inv := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change (β₀ r) • x = r₀ (j₀ (β₀ r)) * x
            rw [Algebra.smul_def]
            rfl } }
      hom_inv_id := by rfl
      inv_hom_id := by rfl }

/-- 概要：実商環上の基底変更を制限すると、既存の実三因子還元に一致する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional :
    (boundedAboveDerivedRestrictScalars q₀).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f) ≅
      PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f :=
  (boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _


/-- 概要：実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedRestrictedH0Iso_of_unconditional (hf : f.Monic) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional W hW f)) ≪≫
    powerRootPrismMonicSourceCoefficientResidueHomologyZeroIso_of_unconditional
      W hW f hf

/-- 概要：無限根モニック入力について、実商環上の還元そのものの非零次数ホモロジーが消える。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) := by
  have hz := powerRootPrismMonicSourceCoefficientResidue_homology_isZero_of_unconditional
    W hW f hf i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional W hW f)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

set_option maxHeartbeats 800000 in
-- 無限根自由 δ 源の二つの制限スカラー作用と商の H⁰ 比較を同時に照合するため。
/-- 概要：実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedH0Iso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) ≅
      ModuleCat.of Q₀ Res₀ := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := powerRootPrismMonicSourceQuotientDerivedRestrictedH0Iso_of_unconditional
    W hW f hf ≪≫
      (powerRootPrismMonicSourceQuotientResidueRestrictionIso_of_unconditional W hW f).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

local notation "X₀" => PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f

/-- 概要：無限根モニック入力の実商還元は、標準t構造の非負部分に属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_isGE_zero_of_unconditional
    (hf : f.Monic) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    W hW f hf i (by omega)

/-- 概要：同じ入力の下で標準t構造の非正部分にも属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_isLE_zero_of_unconditional
    (hf : f.Monic) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    W hW f hf i (by omega)

/-- 概要：実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedSingleIso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := powerRootPrismMonicSourceQuotientDerived_isGE_zero_of_unconditional W hW f hf
  have := powerRootPrismMonicSourceQuotientDerived_isLE_zero_of_unconditional W hW f hf
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (powerRootPrismMonicSourceQuotientDerivedH0Iso_of_unconditional W hW f hf)



end SerrePositivity.BhattScholze.Andre

end PowerRootQuotientDerived

/-! ## 元の A 係数における無限根源の実 (p,d) 還元

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の無限根モニック源について、
A/(p,d) に沿う実導来還元を、同じ raw 残余商の single 対象へ同定する。

## 方針
自由な無限根環と自由 δ 環の A 自由性で導来係数商の正方形を比較し、
全残余源の hpR なしの Koszul・Tor 計算を用いる。

## 規約
元の A 係数作用を保持し、raw 包をねじれ除去商へ変更しない。

## 使われ方
元の実逐次完備化の生成元冪商の有界ねじれ・純性による hpR 解消へ渡す。
-/

@[expose] public noncomputable section PowerRootAResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "C₀" => algebraMap A L₀
local notation "dP" => algebraMap A P₀ W.generator
local notation "I₀" => Ideal.span {(p : A), W.generator}
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk K₀

/-- 概要：元の係数イデアル (p,d) の拡張は無限根自由 δ 源の実 (p,dP) イデアル。
方針：二元生成イデアルの像と係数射の定義を計算する。
規約：prism の完全性も hpR も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数還元の正確な型の照合。 -/
theorem powerRootSourcePDIdeal_map_of_unconditional : (I₀).map C₀ = K₀ := by
  rw [Ideal.map_span, Set.image_pair, map_natCast]
  rfl

/-- 概要：A/(p,d) から元の自由 δ 源の実残余商への標準係数射。
方針：拡張イデアルの等式で元の A 係数射を商へ降下する。
規約：元の全係数の像を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余商の元の基底作用。 -/
def powerRootSourceQuotientCoefficientMap_of_unconditional : R₀ →+* Q₀ :=
  Ideal.quotientMap K₀ C₀ (by
    rw [← powerRootSourcePDIdeal_map_of_unconditional W]
    exact Ideal.le_comap_map)
local notation "κ₀" => powerRootSourceQuotientCoefficientMap_of_unconditional W

/-- 概要：元の A/(p,d) 導来還元と実自由 δ 源商の導来還元の係数制限は同型。
方針：自由な係数代数の一般正方形比較を拡張イデアルの等式で移す。
規約：実導来対象と射影モデルだけを引数にし、hpR を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A 作用に沿う実剰余比較。 -/
def powerRootSourcePDDerivedSquareIso_of_unconditional
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (M : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  let : Module.Free A P₀ := inferInstance
  let : Module.Free A L₀ := Module.Free.trans (R := A) (S := P₀) (M := L₀)
  let F (J : Ideal L₀) :=
    Σ' h : I₀ ≤ J.comap C₀,
      letI := Ideal.Quotient.algebraQuotientOfLEComap h
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
          ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
        (boundedAboveDerivedRestrictScalars (algebraMap (A ⧸ I₀) (L₀ ⧸ J))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X)
  let e : F ((I₀).map C₀) :=
    ⟨Ideal.le_comap_map, freeCoefficientDerivedSquareIso I₀ X M⟩
  let e' : F K₀ := Eq.mp
    (congrArg F (powerRootSourcePDIdeal_map_of_unconditional W)) e
  letI := Ideal.Quotient.algebraQuotientOfLEComap e'.1
  have hκ : algebraMap (A ⧸ I₀) Q₀ = κ₀ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    rfl
  simpa only [hκ] using e'.2

variable (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)
local notation "LCoef" => C₀

/-- 概要：一般モニック f/d 包の実二因子導来対象を元の係数環 A へ制限する。
方針：二重多項式係数包含に沿う既存の導来係数制限を適用する。
規約：有限性やモニック性は対象の定義には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環上の実 prismatic 源。 -/
abbrev PowerRootPrismMonicSourceCoefficientObject_of_unconditional :=
  (boundedAboveDerivedRestrictScalars LCoef).obj X₀

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- 実二因子の具体的な射影テンソルモデルと二重係数商の作用を同時に照合するため。
/-- 概要：元の A/(p,d) に沿う実還元は、実自由 δ 源商上の還元の係数制限と同型。
方針：二重多項式源に対する既存の一般導来係数正方形比較を再利用する。
規約：正方形比較自体にはモニック性も有限性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余の元の係数作用への比較。 -/
def powerRootPrismMonicSourceCoefficientPDReductionIso_of_unconditional :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f) := by
  with_reducible exact (powerRootSourcePDDerivedSquareIso_of_unconditional W X₀
    (boundedAboveDerivedTensorModel
      (boundedAboveDerivedSingleFunctor.obj Mβ) (boundedAboveDerivedSingleFunctor.obj Mα)))

local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀))
  (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)

/-- 概要：元のA上の実モニック族添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact powerRootPrismMonicSourceCoefficientPDReductionIso_of_unconditional W hW f ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (powerRootPrismMonicSourceQuotientDerivedSingleIso_of_unconditional W hW f hf) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 概要：元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional W hW f hf)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 概要：元のA上の実(p,d)還元の非零次数ホモロジーは零。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem powerRootPrismMonicSourceCoefficientPDResidue_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional W hW f hf)))


end SerrePositivity.BhattScholze.Andre

end PowerRootAResidue

/-! ## A1-d：無限根初期係数商と通常モニック商

## 概要
P/(p,dP,f(Y₀)) を A/(p,d) 上の通常モニック無限根商と比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw 残余商へ渡す係数の忠実平坦性。

## 方針
係数商と無限根環の交換を用い、同じ f の関係を課してから係数作用を照合する。

## 規約
d は任意の係数元。hpR、係数商の非零性、追加の平坦性は仮定しない。

## 使われ方
完全 prism の d に適用して、元の raw 残余商への忠実平坦性と合成する。
-/

@[expose] public noncomputable section Comparison

namespace SerrePositivity.BhattScholze.Andre.InitialCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (d : A) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "y" => powerRootMonicPDInput p f
local notation "I" => Ideal.span {(p : A), d}
local notation "R" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "IP" => Ideal.map (algebraMap A P) I
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (algebraMap A P d) a
local notation "Q" => P ⧸ J
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "ybar" => powerRootPolynomialBaseMap R p hp (f.map q)
local notation "M" => PowerRootPolynomialQuotient R p hp (f.map q)

/-- 概要：初期係数イデアルは係数 (p,d) の拡張と f(Y₀) の関係の和。
方針：一元分子族の像と二元係数イデアルの像を展開する。
規約：モニック性や正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の同じ通常商の比較。 -/
theorem initialCoefficientIdeal_eq : J = IP ⊔ Ideal.span {y} := by
  rw [deltaDivisionFirstBaseIdeal, Ideal.map_span, Set.image_pair, map_natCast]
  congr 1
  apply congrArg Ideal.span
  ext z
  simp

/-- 概要：初期係数商は係数商上で f(Y₀) を零にする無限根環と環同型。
方針：係数商と関係商の順序を交換し、係数還元の入力評価公式を使う。
規約：通常の元の商を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常モニック商への係数比較。 -/
def initialCoefficientPrincipalEquiv : Q ≃+* Pbar ⧸ Ideal.span {ybar} := by
  let e := powerRootCoefficientIdealQuotientEquiv A p hp I
  have he : e (Ideal.Quotient.mk IP y) = ybar := by
    rw [powerRootCoefficientIdealQuotientEquiv_mk]
    unfold powerRootMonicPDInput
    exact powerRootCoefficientIdealQuotientMap_baseMap A p hp I f
  have hmap : (Ideal.span {y}).map (Ideal.Quotient.mk IP) =
      Ideal.span {Ideal.Quotient.mk IP y} := by
    simpa only [Set.image_singleton] using (Ideal.map_span (Ideal.Quotient.mk IP) {y})
  have heIdeal : (Ideal.span {Ideal.Quotient.mk IP y}).map e.toRingHom = Ideal.span {ybar} := by
    have hx : (Ideal.span {Ideal.Quotient.mk IP y}).map e.toRingHom =
        Ideal.span {e (Ideal.Quotient.mk IP y)} := by
      exact (Ideal.map_span e.toRingHom {Ideal.Quotient.mk IP y}).trans
        (congrArg Ideal.span (Set.image_singleton (f := e.toRingHom)))
    exact hx.trans (congrArg (fun t : Pbar => Ideal.span {t}) he)
  let eQ := Ideal.quotientEquiv _ _ e heIdeal.symm
  exact (Ideal.quotEquivOfEq (initialCoefficientIdeal_eq (p := p) d f)).trans
    ((DoubleQuot.quotQuotEquivQuotSup IP (Ideal.span {y})).symm.trans
      ((Ideal.quotEquivOfEq hmap).trans eQ))

/-- 概要：主関係商との比較は元の無限根環の全代表元を保つ。
方針：二重商と係数還元の代表元公式を合成する。
規約：係数・根変数に限定せず全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な係数射の同定。 -/
theorem initialCoefficientPrincipalEquiv_mk (x : P) :
    initialCoefficientPrincipalEquiv (p := p) d f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (powerRootCoefficientIdealQuotientMap A p hp I x) := by
  rfl

/-- 概要：初期係数商を既存の PowerRootPolynomialQuotient そのものへ同定する。
方針：f(Y₀) の主イデアルと通常多項式から拡張した関係イデアルの一致を使う。
規約：モニック性は同型の仮定にしない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存のモニック商基底 API への接続。 -/
def initialCoefficientEquiv : Q ≃+* M :=
  (initialCoefficientPrincipalEquiv (p := p) d f).trans
    (Ideal.quotEquivOfEq (powerRootPolynomialQuotient_ideal R p hp (f.map q)).symm)

/-- 概要：標準モニック商への同型は元の係数を同じ係数商の標準像へ送る。
方針：主関係商の代表元公式と無限根係数還元の公式を使う。
規約：全ての A 係数を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の A/(p,d) 作用の照合。 -/
theorem initialCoefficientEquiv_coeff (x : A) :
    initialCoefficientEquiv (p := p) d f (Ideal.Quotient.mk J (algebraMap A P x)) =
      algebraMap R M (q x) := by
  rw [initialCoefficientEquiv, RingEquiv.trans_apply, initialCoefficientPrincipalEquiv_mk,
    powerRootCoefficientIdealQuotientMap_coeff, Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：A/(p,d) から元の初期係数商への係数射。
方針：通常モニック商の係数射を比較同型で戻す。
規約：次の全係数公式で自然な作用を検証する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 残余商への係数射の合成。 -/
def initialCoefficientBaseMap : R →+* Q :=
  (initialCoefficientEquiv (p := p) d f).symm.toRingHom.comp (algebraMap R M)

/-- 概要：初期係数商の係数射は元の係数の標準商像で与えられる。
方針：係数を保つ比較同型の単射性を使う。
規約：元の A の任意元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な基底作用の保証。 -/
theorem initialCoefficientBaseMap_mk (x : A) :
    initialCoefficientBaseMap (p := p) d f (q x) = Ideal.Quotient.mk J (algebraMap A P x) := by
  apply (initialCoefficientEquiv (p := p) d f).injective
  change initialCoefficientEquiv (p := p) d f ((initialCoefficientEquiv (p := p) d f).symm _) = _
  rw [RingEquiv.apply_symm_apply, initialCoefficientEquiv_coeff]

/-- 概要：自然な係数射による初期係数商の代数構造。
方針：検証済みの係数環射から構成する。
規約：利用時に局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性の型。 -/
@[instance_reducible] def initialCoefficientAlgebra : Algebra R Q :=
  (initialCoefficientBaseMap (p := p) d f).toAlgebra

/-- 概要：通常モニック商との比較は A/(p,d) 代数同型。
方針：係数射の定義から可換性を確認する。
規約：単なる環同型でなく同じ係数作用を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底と忠実平坦性の移送。 -/
def initialCoefficientAlgEquiv :
    let := initialCoefficientAlgebra (p := p) d f
    Q ≃ₐ[R] M := by
  let := initialCoefficientAlgebra (p := p) d f
  exact { initialCoefficientEquiv (p := p) d f with
    commutes' := fun _ => (initialCoefficientEquiv (p := p) d f).apply_symm_apply _ }

/-- 概要：モニック初期係数商は A/(p,d) 上自由。
方針：既存の通常モニック無限根商の基底を係数代数同型で戻す。
規約：正次数・hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期係数商の平坦性。 -/
theorem initialCoefficient_free (hf : f.Monic) :
    let := initialCoefficientAlgebra (p := p) d f
    Module.Free R Q := by
  let := initialCoefficientAlgebra (p := p) d f
  let := powerRootPolynomialQuotient_free R p hp (f.map q) (hf.map q)
  exact Module.Free.of_equiv (initialCoefficientAlgEquiv (p := p) d f).symm.toLinearEquiv

/-- 概要：正次数モニック初期係数商は A/(p,d) 上忠実平坦。
方針：零係数商を分け、非零枝では次数保存と既存のモニック商の忠実平坦性を使う。
規約：係数商の非零性を追加せず、hpR も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 残余商への忠実平坦性の第一段。 -/
theorem initialCoefficient_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := initialCoefficientAlgebra (p := p) d f
    Module.FaithfullyFlat R Q := by
  let := initialCoefficientAlgebra (p := p) d f
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    let := initialCoefficient_free (p := p) d f hf
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    have hdeg' : 0 < (f.map q).natDegree := by simpa only [hf.natDegree_map] using hdeg
    let := powerRootPolynomialQuotient_faithfullyFlat R p hp (f.map q) (hf.map q) hdeg'
    exact Module.FaithfullyFlat.of_linearEquiv R M
      (initialCoefficientAlgEquiv (p := p) d f).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.InitialCoefficient

end Comparison

/-! ## A1-d：元の係数商上の raw 残余商と実還元 H⁰ の忠実平坦性

## 概要
初期係数商の通常モニック比較を一般の raw 残余商の忠実平坦性へ合成する。
BS 著者版 Remark 7.15（著者版 p.62）の A1-b の鎖の第一段を供給する。

## 方針
元の全係数で合成射を照合し、A1-b の自然な係数制限作用と既存 H⁰ 比較へ移す。

## 規約
元の raw 包・実自由 δ 源・係数射を保ち、hpR は仮定しない。

## 使われ方
実逐次完備化の純性と生成元の正則性へ渡す入力。完備化後の主張はここでは証明しない。
-/

@[expose] public noncomputable section RawResidue

namespace SerrePositivity.BhattScholze.Andre.InitialCoefficient
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "Qinit" => P ⧸ deltaDivisionFirstBaseIdeal (p := p) dP a
local notation "R" => A ⧸ Ideal.span {(p : A), W.generator}
local notation "Q₀" => L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "κ" => powerRootSourceQuotientCoefficientMap_of_unconditional W
local notation "ψ" => powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f
local notation "Res" => DeltaAdjoinDivisionResidue E dP a
local notation "hd" => powerRootPrismGenerator_isDistinguished W hW
local notation "hpP" => powerRootPolynomial_primeRegular p hW.p_mul_injective

include hW in
/-- 概要：元の無限根自由 δ 源でも p の乗算は単射。
方針：完全 prism の p 正則性を自由多項式環へ平坦移送する。
規約：prism 商の p 正則性とは異なり、hpR を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般 raw 残余商の既存 API への入力。 -/
theorem freeDelta_prime_regular : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)

local notation "hpL" => freeDelta_prime_regular W hW
local notation "hg" => witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "r" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E dP a)

/-- 概要：初期商を経由した A/(p,d) から raw 残余商への係数射。
方針：検証済みの二つの標準係数射を合成する。
規約：必要な p 正則性・ghost 単射性・distinguished 単元は内部供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数作用での忠実平坦性。 -/
def rawResidueBaseMap : R →+* Res :=
  (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg dP a (hd).unit (hd).unit_spec).comp
    (initialCoefficientBaseMap (p := p) W.generator f)

/-- 概要：合成係数射は元の A の全係数の標準 raw 剰余像に一致する。
方針：初期商と raw 残余商への代表元公式を順に使う。
規約：任意の係数を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な作用の確認。 -/
theorem rawResidueBaseMap_mk (x : A) :
    rawResidueBaseMap W hW f (Ideal.Quotient.mk _ x) = r (j (algebraMap A P x)) := by
  rw [rawResidueBaseMap, RingHom.comp_apply, initialCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：初期商を経由した係数射は A1-b の実源商を経由する係数射と同じ。
方針：A/(p,d) の全代表元で二つの合成を比較する。
規約：初期商 Qinit と自由 δ 源商 Q₀ を同一視しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の受渡し指定の自然な R 作用を保証する。 -/
theorem rawResidueBaseMap_eq_source : rawResidueBaseMap W hW f = (ψ).comp κ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, rawResidueBaseMap_mk]
  change r (j (algebraMap A P x)) = r (j
    (deltaDivisionSourceEval E a (MvPolynomial.C (algebraMap A P x))))
  rw [deltaDivisionSourceEval_C]

/-- 概要：検証済みの自然な係数射による raw 残余商の R 代数構造。
方針：元の合成環射から定める。
規約：既存の自然係数制限作用との一致は上の射の等式で保証する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性の合成。 -/
@[instance_reducible] def rawResidueAlgebra : Algebra R Res :=
  (rawResidueBaseMap W hW f).toAlgebra

/-- 概要：元の raw 残余商は合成係数射によって A/(p,d) 上忠実平坦。
方針：初期商の忠実平坦性と既存の初期商上の raw 残余商の忠実平坦性を合成する。
規約：モニック性・正次数以外の追加仮定を置かない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の A1-b 指定作用への移送の入力。 -/
theorem rawResidueBase_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := rawResidueAlgebra W hW f
    Module.FaithfullyFlat R Res := by
  let := initialCoefficientAlgebra (p := p) W.generator f
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL hg dP a (hd).unit (hd).unit_spec
  let := rawResidueAlgebra W hW f
  let : IsScalarTower R Qinit Res := IsScalarTower.of_algebraMap_eq' rfl
  let := initialCoefficient_faithfullyFlat (p := p) W.generator f hf hdeg
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP hpL hg dP a (hd).unit (hd).unit_spec
  exact Module.FaithfullyFlat.trans R Qinit Res

local notation "MRes" => (CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars κ) (ModuleCat.of Q₀ Res) : ModuleCat R)

/-- 概要：A1-b の指定係数制限作用と初期商経由の作用は同じ元を保つ線形同型で結ばれる。
方針：全係数での合成射の一致をスカラー作用の一致へ移す。
規約：元の Res の元を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正確な受渡し型への忠実平坦性の移送。 -/
def rawResidueRestrictionLinearEquiv :
    letI := (ψ).toAlgebra
    letI : Module Q₀ Res := Algebra.toModule
    letI := rawResidueAlgebra W hW f
    MRes ≃ₗ[R] Res := by
  letI := (ψ).toAlgebra
  letI : Module Q₀ Res := Algebra.toModule
  letI := rawResidueAlgebra W hW f
  refine
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro c x
  change Res at x
  change ψ (κ c) * x = rawResidueBaseMap W hW f c * x
  rw [rawResidueBaseMap_eq_source]
  rfl

/-- 概要：A1-b の指定した κ による係数制限のまま、raw 残余商は忠実平坦。
方針：初期商を経由した忠実平坦性を同じ元を保つ線形同型で移す。
規約：受渡しの正確な型を保ち、hpR を置かない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A 係数の実還元 H⁰ への入力。 -/
theorem rawResidue_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := (ψ).toAlgebra
    letI : Module Q₀ Res := Algebra.toModule
    Module.FaithfullyFlat R MRes := by
  let := (ψ).toAlgebra
  let : Module Q₀ Res := Algebra.toModule
  let := rawResidueAlgebra W hW f
  let := rawResidueBase_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R Res
    (rawResidueRestrictionLinearEquiv W hW f)

/-- 概要：元の A/(p,d) による実導来還元の H⁰ は忠実平坦。
方針：既存の A1-b の実 H⁰ 比較へ指定作用での raw 残余商の忠実平坦性を渡す。
規約：モニック性・正次数だけを追加し、hpR・Tor 消滅・平坦性は追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の A1-b の次の純性・正則性接続への受渡し。 -/
theorem sourceResidueH0_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A), W.generator}))).obj
          (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj) := by
  let := (ψ).toAlgebra
  let : Module Q₀ Res := Algebra.toModule
  let := rawResidue_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R MRes
    (powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional W hW f hf).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.InitialCoefficient

end RawResidue

/-! ## hpR の正則性計算における境界

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の生成元・ϖ 持上げの mod p 正則性は、
完全 prism の商の p 正則性と同値である。

## 方針
正則対の順序交換を両向きに使う。ϖ 持上げには x^p=d modulo p を使う。
有界ねじれは無条件に供給するが、正則性への強化はしない。

## 規約
原典は基底変更で p ねじれなしの場合へ帰着している。
一般の perfectoid 商で hpR が自動的に成立するという主張はしない。

## 使われ方
hpR を外せる分冪降下と、正則性自体を主張する既存補題を区別する。
-/

@[expose] public noncomputable section RegularityBoundary

namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：完全 prism の生成元の mod p 正則性は商の p 正則性と同値。
方針：完全 δ 環の p 正則性を使って、既存の順序交換を逆向きにも適用する。
規約：有界 p ねじれだけでこの同値の右辺を得たとは扱わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の hpR を保持する正則性補題の判定。 -/
theorem perfectPrism_generator_modPrime_regular_iff
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) W.generator) ↔
      IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal) := by
  constructor
  · intro hd
    have ht := principal_regular_swap (p : A) W.generator hW.p_mul_injective hd
    simpa only [OrientedPrism.ideal, map_natCast] using ht
  · exact perfectPrism_generator_modPrime_regular W

/-- 概要：ϖ 持上げの mod p 正則性も商の p 正則性と同値。
方針：x^p=d modulo p と正の冪の正則性の同値を、生成元の判定へ渡す。
規約：零環も含み、prism 商の追加仮定を導入しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の旧正則係数降下の必要条件を明示する。 -/
theorem perfectPrismVarpiLift_modPrime_regular_iff
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) ↔
      IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal) := by
  constructor
  · intro hx
    apply (perfectPrism_generator_modPrime_regular_iff W hW).mp
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {(p : A)}))
      (perfectPrismVarpiLift_frobenius W hW)
    rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul] at h
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)),
      zero_mul, add_zero] at h
    rw [← h]
    exact hx.pow p
  · exact perfectPrismVarpiLift_modPrime_regular W hW

/-- 概要：完全 prism の任意生成元冪商の p 冪ねじれは既定の冪で消える。
方針：完全性・生成元の distinguished 性と正則性を既存の冪ねじれ定理へ供給する。
規約：hpR を仮定せず、p 正則性とは区別する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化比較に使える無条件の弱い入力。 -/
theorem perfectPrism_generator_power_bounded_torsion_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (n N : ℕ) (x : A ⧸ Ideal.span {W.generator ^ n})
    (hx : (p : A ⧸ Ideal.span {W.generator ^ n}) ^ N * x = 0) :
    (p : A ⧸ Ideal.span {W.generator ^ n}) ^ n * x = 0 := by
  let := W.isAdicComplete_p_of_perfect hW
  exact hW.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (W.isDistinguished_generator) n N x hx

omit [Fact p.Prime] in
/-- 概要：非零な標数 p 環では p の乗算は単射でない。
方針：1 と 0 の像が一致することを単射性に渡す。
規約：有界 p ねじれ・被約性から hpR は従わないことを説明するための一般補題。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底変更前の正則性を誤って仮定しないための境界。 -/
theorem not_prime_regular_of_charP (R : Type u) [CommRing R] [Nontrivial R]
    [CharP R p] : ¬ IsSMulRegular R (p : R) := by
  intro hp
  exact one_ne_zero (hp (by simp only [CharP.cast_eq_zero R p, smul_eq_mul, zero_mul]))

end SerrePositivity.BhattScholze.Andre

end RegularityBoundary

/-! ## 原典の R/ϖ における標数条件の自動供給

## 概要
PowerRootMonicPDFlat の hpR は p 正則性ではなく p=0 を意味する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の R/ϖ ではこの条件を内部で供給できる。

## 方針
(ϖ^p)=(p) から p∈(ϖ) を得て、既存の自由性・忠実平坦性を適用する。

## 規約
prism 商の p 正則性や非零性を追加しない。

## 使われ方
係数条件を呼出し側へ残さず、原典の通常分冪環の平坦性を使う。
-/

@[expose] public noncomputable section MonicPDFlat

namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "R" => A ⧸ W.ideal
local notation "Rv" => R ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk W.ideal)

/-- 概要：原典の R/ϖ では p が零。
方針：(ϖ^p)=(p) と (ϖ^p)⊆(ϖ) を組み合わせる。
規約：prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の通常分冪表示への標数条件の供給。 -/
theorem perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional : (p : Rv) = 0 := by
  have hle : Ideal.span {perfectPrismVarpi W hW ^ p} ≤
      Ideal.span {perfectPrismVarpi W hW} := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) p
      (Nat.Prime.pos (Fact.out : p.Prime))
  rw [perfectPrismVarpi_span_pow W hW] at hle
  have hm := hle (Ideal.mem_span_singleton_self (p : R))
  simpa only [map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

/-- 概要：R/ϖ 上のモニック無限根分冪表示環は自由。
方針：原典の係数商の p=0 を内部で証明して既存の自由性へ渡す。
規約：正次数も prism 商の p 正則性も不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実係数環上の自由性。 -/
theorem powerRootMonicDPPresentation_free_of_unconditional
    (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (PrincipalDPPresentation Nv
      (powerRootPolynomialBaseMap Rv p hp (f.map bv))) :=
  powerRootMonicDPPresentation_free Rv p hp (Fact.out : p.Prime)
    (perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional W hW) (f.map bv) (hf.map bv)

/-- 概要：R/ϖ 上の正次数モニック無限根分冪表示環は忠実平坦。
方針：p=0 と、係数商後のモニック性・正次数を既存の忠実平坦性へ供給する。
規約：原典の正次数条件を保持し、非零性を追加しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の通常代数の忠実平坦性。 -/
theorem powerRootMonicDPPresentation_faithfullyFlat_of_unconditional
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat Rv (PrincipalDPPresentation Nv
      (powerRootPolynomialBaseMap Rv p hp (f.map bv))) :=
  perfectPrismVarpiNativePDEnvelope_faithfullyFlat W hW f hf hdeg

end SerrePositivity.BhattScholze.Andre

end MonicPDFlat

/-! ## 元の raw 包の最初の有限段の p 正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の無限根モニック入力について、深さ零の実関係商は p 正則。

## 方針
定数係数が正則な一次多項式の非零因子判定を、元の mod p 関係に適用する。

## 規約
hpR と分母の mod p 正則性は不要。後続有限段と raw 全体の p 正則性はここでは主張しない。

## 使われ方
残る raw p 正則性の有限段帰納法の初期値を無条件に供給する。
-/

@[expose] public noncomputable section RawInitialRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：定数係数が正則な一次多項式は正則。
方針：一つの係数の非零因子性から多項式の非零因子性を得る。
規約：一次係数の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期線形関係の p 飽和性。 -/
theorem unconditionalLinearPolynomial_regular_of_constant
    {R : Type u} [CommRing R] (c b : R) (hb : IsSMulRegular R b) :
    IsSMulRegular (Polynomial R) (Polynomial.C c * Polynomial.X + Polynomial.C b) := by
  have hb' : b ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_left.mpr (fun x hx => hb (hx.trans (mul_zero b).symm))
  have h : Polynomial.C c * Polynomial.X + Polynomial.C b ∈ nonZeroDivisors (Polynomial R) :=
    Polynomial.mem_nonZeroDivisors_of_coeff_mem 0 (by simpa using hb')
  exact (isRegular_iff_mem_nonZeroDivisors.mpr h).left

/-- 概要：指定変数の定数係数正則な一次式は、多変数多項式環でも正則。
方針：指定変数を分離し、残りの変数への平坦拡大で係数正則性を保つ。
規約：変数族の有限性と一次係数の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の自由 δ 環の初期関係。 -/
theorem unconditionalLinearMvPolynomial_regular_of_constant
    {R : Type u} [CommRing R] {τ : Type v} (c b : R) (s : τ) (hb : IsSMulRegular R b) :
    IsSMulRegular (MvPolynomial τ R)
      (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hb' := hb.of_flat (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := unconditionalLinearPolynomial_regular_of_constant
    (MvPolynomial.C c) (MvPolynomial.C b) hb'
  intro x y hxy
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxy

section Initial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type u} [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "qP" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "qL" => Ideal.Quotient.mk (Ideal.span {(p : L)})
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) 0
local notation "B" => L ⧸ Ideal.span {g}

/-- 概要：正則な分子の mod p 像だけで、最初の実 δ 関係は mod p で正則。
方針：自由環の実 mod p 同型で定数係数正則な一次式へ移す。
規約：分母の mod p 正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の関係商の p 正則性。 -/
theorem unconditionalDeltaDivisionUnaryFirst_mod_prime_regular
    (ha : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (qP (a default))) :
    IsSMulRegular (L ⧸ Ideal.span {(p : L)}) (qL g) := by
  apply (ringEquiv_isSMulRegular
    (relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)) _).mpr
  rw [relativeFreeModPrimePolynomialEquiv_first]
  have hn : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (-(qP (a default))) := by
    intro x y hxy
    apply ha
    simpa only [neg_smul, neg_inj] using hxy
  simpa only [map_neg, sub_eq_add_neg] using
    unconditionalLinearMvPolynomial_regular_of_constant (qP d) (-(qP (a default)))
      ((default : σ), 0) hn

/-- 概要：元の最初の関係商は、正則な分子の mod p 像だけで p 正則。
方針：自由源の p 正則性と初期関係の mod p 正則性で順序交換する。
規約：分母の mod p 正則性を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根モニック有限段の初期値。 -/
theorem unconditionalDeltaDivisionUnaryFirst_prime_regular
    (hpA : IsSMulRegular A (p : A))
    (ha : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (qP (a default))) :
    IsSMulRegular B (p : B) := by
  have hpL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hpA.of_flat (S := L)
  have h := principal_regular_swap (p : L) g hpL
    (unconditionalDeltaDivisionUnaryFirst_mod_prime_regular D d a ha)
  simpa only [map_natCast] using h
end Initial

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => PowerRootUnaryFreeDeltaRing A p hp
local notation "I" => deltaDivisionFiniteRelationIdeal E dP a

/-- 概要：無限根モニック raw 包の深さ零の実有限関係商は p 正則。
方針：既存のモニック入力の mod p 正則性を初期関係の定数係数判定へ渡す。
規約：hf のみを要求し、hpR と正次数を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw p 正則性の有限段帰納法の初期値。 -/
theorem powerRootPrismMonicFinite_prime_regular_zero_of_unconditional (hf : f.Monic) :
    IsSMulRegular (L ⧸ I 0) (p : L ⧸ I 0) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have ha : IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) (a default)) := by
    simpa only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput] using
      powerRootPolynomial_monic_mod_prime_regular A p hp f hf
  have h := unconditionalDeltaDivisionUnaryFirst_prime_regular E dP a hpP ha
  let e := Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_zero E dP a).symm
  have ht := (ringEquiv_isSMulRegular e (p : _)).mp h
  simpa only [map_natCast] using ht

/-- 概要：無限根モニック入力の最初の mod p 線形関係は、hpR なしに正則。
方針：分子のモニック性から定数係数の正則性を供給する。
規約：任意の変数族を許し、元の非モニック一般形まで無条件化したとはしない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック入力における旧補題の置換先。 -/
theorem powerRootPrismFirstModPrimeRelation_regular_of_monic_unconditional
    (hf : f.Monic) {τ : Type v} (s : τ) :
    IsSMulRegular (MvPolynomial τ (P ⧸ Ideal.span {(p : P)}))
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : P)}) dP) * MvPolynomial.X s -
        MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) := by
  have ha : IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (-(Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) := by
    have hr := powerRootPolynomial_monic_mod_prime_regular A p hp f hf
    intro x y hxy
    apply hr
    simpa only [powerRootMonicPDInput, neg_smul, neg_inj] using hxy
  simpa only [map_neg, sub_eq_add_neg] using
    unconditionalLinearMvPolynomial_regular_of_constant
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) dP)
      (-(Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) s ha

end SerrePositivity.BhattScholze.Andre

end RawInitialRegular
