module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionResidue
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalPair
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Source
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.RawRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionWitt
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion

/-!
# 完備化 prism と Hodge–Tate 候補の普遍性

## 概要
raw 包の正則対と完備化の p 正則性、Hodge–Tate 候補の基底射・根・ϖ 剰余、raw 包の完備化 prism とその普遍性、生成元正則性を明示した prism 構造、互換根データ・剰余根データ・基底 prism 射・方程式入力に対する普遍性。
BS 著者版 Proposition 3.13 の包の普遍性をモニック根の入力で扱うため、完備化 prism とその商を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/FrobeniusPullback`、`PowerRootEnvelope/InputUniversal`、`PowerRootEnvelope/PerfectionFaithful`、`PowerRootEnvelope/Unconditional/FrobeniusPD`、`PowerRootEnvelope/VarpiComparison`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## 無限根モニック raw 包の正則対

## 概要

p 正則な prism 商を持つ完全 prism 上の無限根モニック raw 包で、p と mod p の分母は正則。
BS 著者版 Remark 7.15（著者版 p.62）の実完備化前の計算。

## 方針

有限段の分母正則性を実 δ 閉包商の mod p に移す一般結果へ、prism とモニック性を供給する。

## 規約

正次数は要求しない。raw と mod p の中間主張では prism 商の p 正則性を明示する。
通常 p 完備化の正則対と実二座標完備化の分母正則性にはこの仮定を要求しない。
通常 p 完備化の旧宣言は削除し、実源の純性と標準 H⁰ 比較による
Unconditional.RawPAdicPairRegular の公開名を使う。原典とは異なる証明経路。

## 使われ方

元の raw 包の実完備化への正則対保存の入力。
-/

@[expose] public noncomputable section PowerRootPrismMonicRawPairRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "Raw" => DeltaAdjoinDivision E dP a

include hpR hf in
/-- 概要：無限根モニック raw 包の mod p で prism 生成元の像は正則。
方針：prism 正則対とモニック入力を供給し、有向上限で得た分母飽和性を使う。
規約：元の δ 閉包商を使い、正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化前の正則対の第二成分。 -/
theorem powerRootPrismMonicRaw_mod_prime_generator_regular :
    IsSMulRegular (Raw ⧸ Ideal.span {(p : Raw)})
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (deltaAdjoinDivisionMap E dP a dP)) := by
  have hpP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)
  let v := (powerRootPrismGenerator_isDistinguished W hW).unit
  have hv : (v : P) = (E).delta dP :=
    (powerRootPrismGenerator_isDistinguished W hW).unit_spec
  exact deltaDivisionUnaryRaw_mod_prime_d_regular E dP a hpP
    (powerRootPrismGenerator_modPrime_regular p W hW hpR)
    (powerRootPrismMonic_modPrime_generator_regular p W f hf) hgL v hv

include hf in
/-- 概要：無限根モニック raw 包の実二座標完備化 H⁰ で分母の像は正則。
方針：分冪包 の実源の純性と次数零モニック入力の零環性から得た正則性を使う。
原典の p ねじれなしへの帰着とは異なる純性による経路。
規約：元の Koszul 完備化 H⁰ と標準射を保持し、hpR・正次数を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の分母ねじれの排除。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular :
    let dL := deltaAdjoinDivisionMap E dP a dP
    letI := SerrePositivity.DerivedCompletion.pdCompletionCommRing Raw p dL
    IsSMulRegular (SerrePositivity.DerivedCompletion.PDCompletionH0 Raw p dL)
      (SerrePositivity.DerivedCompletion.pdCompletionUnit Raw p dL dL) := by
  exact powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional W hW f hf

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicRawPairRegular

/-! ## 無限根モニック実完備化と Hodge–Tate 商の p 正則性

## 概要

完全 prism 上の無限根モニック raw 包の実 (p,d) 完備化 H⁰ は p 正則。
prism 商が p 正則なら、その分母商も p 正則。BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合。

## 方針

H⁰ の p 正則性は 分冪包 の実源の純性から供給する。分母商については
元の raw 包の p,d 正則対を実反復完備化と標準剰余比較に移す。

## 規約

元の Koszul 完備化 H⁰ と標準射を使う。分母商の結果では prism 商の p 正則性を明示する。
H⁰ の結果自体にはこの仮定は不要で、正次数も要求しない。

## 使われ方

原典の prismatic 源との同定、および Hodge–Tate 商の p 完全忠実平坦性への入力。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "dL" => deltaAdjoinDivisionMap E dP a dP
local notation "H" => PDCompletionH0 Raw p dL

include hf in
/-- 概要：無限根モニック raw 包の実二座標完備化 H⁰ は p 正則。
方針：分冪包 の実源の純性と次数零モニック入力の零環性による正則性を使う。
原典の p ねじれなしへの帰着とは異なる純性による経路。
規約：prism 商の p 正則性も正次数も仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化に新しい p ねじれがないこと。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular H (p : H) := by
  exact powerRootPrismMonic_pdCompletion_prime_regular_of_unconditional W hW f hf

include hpR hf in
/-- 概要：無限根モニック実完備化の分母商は p 正則。
方針：raw 包の正則対へ実二座標完備化の第二元商での第一元正則性を適用する。
規約：実 H⁰ の標準分母像で割る通常商を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Hodge–Tate 候補の p ねじれの排除。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular (H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
      (p : H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}) := by
  have h := principalPair_pairCompletion_mod_second_first_regular (p : Raw) dL
    (powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf)
    (powerRootPrismMonicRaw_mod_prime_generator_regular W hW hpR f hf)
  let := pdCompletionCommRing Raw p dL
  change IsSMulRegular (H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
    (Ideal.Quotient.mk (Ideal.span {pdCompletionUnit Raw p dL dL})
      (pdCompletionUnit Raw p dL (p : Raw))) at h
  simpa only [map_natCast] using h

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletionRegular

/-! ## 無限根モニック Hodge–Tate 候補の基底射と ϖ 商

## 概要

実完備化の分母商 T に prism 商 R から自然な基底射を与え、T の ϖ 商を既存の二元商と同定する。
BS 著者版 Remark 7.15（著者版 p.62）の通常剰余の忠実平坦性への接続。

## 方針

係数射を分母商へ降ろし、標準二重主商同型で生成元と ϖ 持上げの二元商へ移す。

## 規約

元の実完備化と標準係数射を保持する。モニック性はこの比較には不要。

## 使われ方

既存の R/ϖ 上の pd 計算を、自然な R 代数 T の剰余へ移す。
-/

@[expose] public noncomputable section PowerRootPrismMonicHodgeTateBase

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}

/-- 概要：prism 商から実完備化の分母商への自然な基底射。
方針：係数射の生成元像が分母商で零となることを使って降ろす。
規約：モニック性・prism 商の p 正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Hodge–Tate 候補の係数作用。 -/
def powerRootPrismMonicHodgeTateBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    R →+* T := by
  let := pdCompletionCommRing L p (jL dP)
  apply Ideal.Quotient.lift W.ideal ((qH).comp ((uL).comp ((jL).comp (algebraMap A P))))
  change Ideal.span {W.generator} ≤ RingHom.ker _
  apply Ideal.span_le.mpr
  intro r hr
  rcases Set.mem_singleton_iff.mp hr with rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self dH)

/-- 概要：基底射は A の代表元をその標準完備化係数像へ送る。
方針：商への降下の計算規則を使う。
規約：全ての係数元 r を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な作用の照合。 -/
theorem powerRootPrismMonicHodgeTateBaseMap_mk (r : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateBaseMap W hW f (Ideal.Quotient.mk W.ideal r) =
      qH (uL (jL (algebraMap A P r))) := rfl

/-- 概要：基底の ϖ は選んだ持上げの標準像へ送られる。
方針：係数代表元公式を適用する。
規約：ϖ は生成元の逆 Frobenius 像から選ぶ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の T/ϖ の実商比較。 -/
theorem powerRootPrismMonicHodgeTateBaseMap_varpi :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateBaseMap W hW f (perfectPrismVarpi W hW) = qH xH := rfl

/-- 概要：自然な Hodge–Tate 候補の ϖ 商は実完備化の指定二元商と環同型。
方針：ϖ の標準像公式と二重主商同型を使う。
規約：係数射を変えず、モニック性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存 pd 剰余計算の移送。 -/
def powerRootPrismMonicHodgeTateVarpiEquiv :
    let := pdCompletionCommRing L p (jL dP)
    (T ⧸ Ideal.span {powerRootPrismMonicHodgeTateBaseMap W hW f (perfectPrismVarpi W hW)}) ≃+*
      S := by
  let := pdCompletionCommRing L p (jL dP)
  exact principalDoubleQuotEquiv dH xH

/-- 概要：ϖ 商比較は実完備化の代表元を保つ。
方針：二重主商同型の代表元公式を使う。
規約：実 H⁰ の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数線形性の確認。 -/
theorem powerRootPrismMonicHodgeTateVarpiEquiv_mk (t : H) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateVarpiEquiv W hW f
      (Ideal.Quotient.mk _ (qH t)) = Ideal.Quotient.mk _ t := by
  let := pdCompletionCommRing L p (jL dP)
  exact principalDoubleQuotEquiv_mk dH xH t

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicHodgeTateBase

/-! ## 元の無限根入力の Hodge–Tate 候補における実根

## 概要

無限根変数 Y₀ の標準像は、元のモニック入力の prism 商への係数像の根となる。
BS 著者版 Remark 7.15（著者版 p.62）の同じ実候補における根の計算。

## 方針

raw 包の dX=f(Y₀) を実完備化の分母商へ送り、分母像が零となることを使う。

## 規約

根の計算自体はモニック性・正次数・prism 商の p 正則性を要求しない。

## 使われ方

p 完全忠実平坦な具体的候補が元の多項式の根を持つことの確認。
-/

@[expose] public noncomputable section PowerRootPrismMonicHodgeTateRoot

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}


/-- 概要：無限根変数 Y₀ の実完備化分母商への標準像。
方針：元の入力環から raw 包、実完備化、分母商へ順に送る。
規約：係数射と同じ標準射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根を持つ具体的候補。 -/
def powerRootPrismMonicHodgeTateRoot :
    let := pdCompletionCommRing L p (jL dP)
    T := by
  let := pdCompletionCommRing L p (jL dP)
  exact qH (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)))

/-- 概要：指定した標準像は元の入力多項式の prism 商での係数像の根。
方針：raw 関係を分母商へ送り、係数射の一致と多項式評価の自然性を使う。
規約：根の計算にモニック性・正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全忠実平坦な根付き候補。 -/
theorem powerRootPrismMonicHodgeTateRoot_eval :
    let := pdCompletionCommRing L p (jL dP)
    (f.map (Ideal.Quotient.mk W.ideal)).eval₂ (powerRootPrismMonicHodgeTateBaseMap W hW f)
      (powerRootPrismMonicHodgeTateRoot W hW f) = 0 := by
  let := pdCompletionCommRing L p (jL dP)
  let k : P →+* T := (qH).comp ((uL).comp jL)
  have hd : k dP = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self dH)
  have hrel := congrArg (fun z : L => qH (uL z)) (deltaAdjoinDivision_relation E dP a default)
  simp only [map_mul, powerRootPrismMonicUnaryFamily, powerRootMonicPDInput] at hrel
  have hy : k (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p hp f) = 0 := by
    change k dP * qH (uL (deltaAdjoinDivisionVariable E dP a default)) =
      k (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p hp f) at hrel
    rw [hd, zero_mul] at hrel
    exact hrel.symm
  have hcoeff : (powerRootPrismMonicHodgeTateBaseMap W hW f).comp
      (Ideal.Quotient.mk W.ideal) = k.comp (algebraMap A P) := by
    ext r
    exact powerRootPrismMonicHodgeTateBaseMap_mk W hW f r
  rw [Polynomial.eval₂_map, hcoeff]
  change f.eval₂ (k.comp (algebraMap A P)) (k (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)) = 0
  rw [← Polynomial.hom_eval₂]
  exact hy

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicHodgeTateRoot

/-! ## 無限根モニック raw 包の実完備化 prism

## 概要

完全 prism 上で、無限根モニック raw 包の実完備化は
標準分母像を生成元とする oriented prism となる。BS 著者版 Remark 7.15（著者版 p.62）の源候補。

## 方針

既存の実完備化の δ 構造、分母の distinguished 性、検証済みの正則性と導来完備性を結ぶ。
分母正則性は 分冪包 の実源の純性から供給し、原典の p ねじれなしへの帰着とは異なる経路を使う。

## 規約

完全 prism であることは主張しない。原典の prismatic envelope との普遍性比較は別工程。

## 使われ方

同じ具体的候補の p 完全忠実平坦性と根を、prismatic 源の比較へ接続する。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionPrism

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
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

include hf in
/-- 概要：元の無限根モニック実完備化に標準分母像を生成元とする prism 構造を与える。
方針：distinguished 性を二つの標準 δ 射で移し、実完備化の正則性と完備性を使う。
正則性は原典の帰着とは異なる実源の純性による証明から供給する。
規約：prism 商の p 正則性も正次数も要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の prismatic 源との比較の入力。 -/
def powerRootPrismMonicCompletionPrism :
    let := pdCompletionCommRing L p (jL dP)
    OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  have hdL : (DL).IsDistinguished (jL dP) := by
    have h := (powerRootPrismGenerator_isDistinguished W hW).map jL
    rw [deltaAdjoinDivisionMap_isDeltaHom E dP a dP] at h
    exact h
  have hdH : (DH).IsDistinguished (uL (jL dP)) := by
    have h := hdL.map uL
    rw [pdCompletionUnit_isDeltaHom DL (jL dP) (jL dP)] at h
    exact h
  exact OrientedPrism.ofDistinguished DH (uL (jL dP)) hdH
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf)
    (pdCompletionH0_self_complete_p L p (jL dP))
    (pdCompletionH0_self_complete_d L p (jL dP))

/-- 概要：元の係数 prism の台環から実完備化への標準射。
方針：無限根係数射、raw 射、実完備化単位を合成する。
規約：環射自体にモニック性や p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底 prism 上の比較。 -/
def powerRootPrismMonicCompletionBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    A →+* H := by
  let := pdCompletionCommRing L p (jL dP)
  exact (uL).comp ((jL).comp (algebraMap A P))

/-- 概要：標準係数射は元の δ 構造と実完備化の δ 構造を保つ。
方針：三つの既存の標準 δ 射を合成する。
規約：元の指定 δ 構造を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の prism 射の δ 条件。 -/
theorem powerRootPrismMonicCompletionBaseMap_isDeltaHom :
    let := pdCompletionCommRing L p (jL dP)
    W.deltaStructure.IsDeltaHom DH (powerRootPrismMonicCompletionBaseMap W hW f) := by
  let := pdCompletionCommRing L p (jL dP)
  exact (pdCompletionUnit_isDeltaHom DL (jL dP)).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E dP a).comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective W.deltaStructure))

include hf in
/-- 概要：標準係数射は指定 prism 生成元を実完備化 prism の指定生成元へ送る。
方針：双方の標準射と生成元の定義を展開する。
規約：生成元は変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底 prism 上の比較。 -/
theorem powerRootPrismMonicCompletionBaseMap_generator :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicCompletionBaseMap W hW f W.generator =
      (powerRootPrismMonicCompletionPrism W hW f hf).generator := rfl

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletionPrism

/-! ## André 生成元正則性を明示した元の H の prism 構造

## 概要

元の H の標準分母像の正則性が供給されると、同じ H はその像を生成元とする prism となる。
基底からの標準射も prism 射になる。BS 著者版 Remark 7.15（著者版 p.62）の源の合流点。

## 方針

標準 δ 射で distinguished 性を移し、既存の導来完備性と指定された正則性を組み合わせる。
原典を補う raw 実完備化の明示的な構造による経路。

## 規約

正則性 hreg は明示引数とし、ここでは解消しない。hpR・モニック性で代用しない。
既存の hpR 付き定理を変更せず、別名で合流先を用意する。

## 使われ方

並列の生成元正則性の成果を受け取り、元の H の prism 射による初期性へ接続する。
-/

@[expose] public noncomputable section PowerRootPrismMonicRegularSource

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

local notation "dH" => uL (jL dP)
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f

/-- 概要：標準分母像が正則なら元の H を prism として構成できる。
方針：distinguished 性を raw 射と完備化単位で移し、二方向の導来完備性を使う。
規約：hreg を明示し、完全 prism とは主張しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の源の prism 化への条件付き接続点。 -/
def powerRootPrismMonicCompletionPrismOfRegular :
    let := pdCompletionCommRing L p (jL dP)
    IsSMulRegular H dH → OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  have hdL : (DL).IsDistinguished (jL dP) := by
    have h := (powerRootPrismGenerator_isDistinguished W hW).map jL
    rw [deltaAdjoinDivisionMap_isDeltaHom E dP a dP] at h
    exact h
  have hdH : (DH).IsDistinguished dH := by
    have h := hdL.map uL
    rw [pdCompletionUnit_isDeltaHom DL (jL dP) (jL dP)] at h
    exact h
  exact OrientedPrism.ofDistinguished DH dH hdH hreg
    (pdCompletionH0_self_complete_p L p (jL dP))
    (pdCompletionH0_self_complete_d L p (jL dP))

/-- 概要：条件付き prism の生成元は元の標準分母像そのもの。
方針：構成の生成元の定義を確認する。
規約：orientation を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H/d の保持。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_generator :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).generator = dH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：条件付き prism の δ 構造は元の実完備化の δ 構造。
方針：構成の δ 構造の定義を確認する。
規約：台環も δ 構造も取り替えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存の δ 普遍射との接続。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_deltaStructure :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).deltaStructure = DH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：条件付き prism のイデアルは元の標準分母像の主イデアル。
方針：元の orientation による prism イデアルの定義を使う。
規約：同じ H/d を標準商として使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存の標準入力作用の保持。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_ideal :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).ideal = Ideal.span {dH} := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：元の基底射は条件付き構成した H の prism への射となる。
方針：既存の δ 保存性と標準生成元像によるイデアル保存性を組み合わせる。
規約：基底の指定生成元を元の標準分母像へ送る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底 prism 上の源。 -/
def powerRootPrismMonicCompletionPrismBaseHomOfRegular :
    let := pdCompletionCommRing L p (jL dP)
    (hreg : IsSMulRegular H dH) →
      OrientedPrism.Hom W (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  refine ⟨baseH, powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f, ?_⟩
  change Ideal.span {W.generator} ≤ (Ideal.span {dH}).comap baseH
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = W.generator := Set.mem_singleton_iff.mp hx
  rw [hxd]
  exact Ideal.mem_span_singleton_self dH

/-- 概要：条件付き基底 prism 射の台の環射は元の標準係数射。
方針：構成の環射の定義を使う。
規約：係数作用を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底保存条件の照合。 -/
theorem powerRootPrismMonicCompletionPrismBaseHomOfRegular_toRingHom :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg).toRingHom = baseH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicRegularSource

/-! ## 具体的な実完備化 prism の普遍性と一段構成比較

## 概要

無限根モニック実完備化 prism は、指定した入力 δ 射と分子の可除性を持つ試験 prism へ
一意に写る。さらに旧分母ねじれ除去を挟む既存一段構成と環同型となる。
BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の比較の代数的部分。

## 方針

試験 prism の正則性と完備性を raw 実完備化の一般普遍性に供給する。
自分自身で証明した分母正則性から旧ねじれ除去の標準比較を適用する。
その正則性は原典と異なる実源の純性による経路で供給する。

## 規約

無限根入力環からの δ 射を指定する相対的普遍性である。
prism 商の p 正則性や正次数は要求しない。
原典の絶対 prismatic envelope の同定は、この入力射の一意持上げとの接続を要する。

## 使われ方

元の実候補を既存の一段 δ 完全化へ渡すための係数を保つ比較。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionUniversal

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
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


include hf in
/-- 概要：指定入力 δ 射と可除性を持つ試験 prism への射は一意に存在する。
方針：試験 prism の正則性・p 完備性・生成元完備性を一般の raw 普遍性へ渡す。
規約：生成元の像の一致を明示し、入力射自体は指定する。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の相対 envelope 比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hg : (E).IsDeltaHom Q.deltaStructure g) (hd : g dP = Q.generator)
    (ha : Q.generator ∣ g (powerRootMonicPDInput p f)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
        Q.deltaStructure F ∧ F.comp ((uL).comp jL) = g := by
  let := pdCompletionCommRing L p (jL dP)
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hd]
    exact Q.generator_regular
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hd]
    exact Q.complete_generator
  have ha' : ∀ s, g dP ∣ g (a s) := by
    intro s
    change g dP ∣ g (powerRootMonicPDInput p f)
    rw [hd]
    exact ha
  have h := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg hr ha'
    Q.complete_p hc
  change ∃! F : H →+* B, (DH).IsDeltaHom Q.deltaStructure F ∧
    F.comp ((uL).comp jL) = g
  exact h

include hf in
/-- 概要：元の無限根モニック実完備化は旧ねじれ除去後の既存一段実完備化と環同型。
方針：自分自身の分母正則性を一般の標準比較に供給する。
規約：元の実 H⁰ を源とし、比較先の正則性を追加仮定しない。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の一段構成との接続。 -/
def powerRootPrismMonicCompletionTorsionEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    H ≃+* DerivedDeltaDivisionCompletion E dP a := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf)

include hf in
/-- 概要：一段構成比較は無限根入力環の標準係数像を保つ。
方針：一般比較の raw 代表元公式を標準入力射に適用する。
規約：全ての入力環元を扱う。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の後続 δ 完全化比較。 -/
theorem powerRootPrismMonicCompletionTorsionEquiv_coeff (r : P) :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    powerRootPrismMonicCompletionTorsionEquiv W hW f hf (uL (jL r)) =
      derivedDeltaDivisionMap E dP a r := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv_unit E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf) (jL r)

include hf in
/-- 概要：具体的な一段構成比較は実完備化 prism の δ 構造を保つ。
方針：一般比較の δ 性へ分母正則性を供給する。
規約：原典の絶対 envelope との比較は別工程。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の既存 δ 完全化への接続。 -/
theorem powerRootPrismMonicCompletionTorsionEquiv_isDeltaHom :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
      (derivedDeltaDivisionStructure E dP a)
      (powerRootPrismMonicCompletionTorsionEquiv W hW f hf).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv_isDeltaHom E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf)

include hf in
/-- 概要：入力射と両立する比較射は指定 prism 生成元を保つ。
方針：入力環上の合成等式を分母で評価する。
規約：射の δ 性に依存しない生成元の計算。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の相対 prism 射の条件。 -/
theorem powerRootPrismMonicCompletionHom_generator
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hd : g dP = Q.generator) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ F : H →+* B, F.comp ((uL).comp jL) = g →
      F (powerRootPrismMonicCompletionPrism W hW f hf).generator = Q.generator := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF
  exact (RingHom.congr_fun hF dP).trans hd

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletionUniversal

/-! ## 互換な rank 1 根データによる実完備化の普遍射

## 概要

元の raw 実完備化から試験 prism への射を、無限根入力 δ 射の指定を使わず、
基底 δ 射・互換な rank 1 根列・モニック入力の可除性から一意に作る。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope 比較へ向けた入力射の具体化。

## 方針

有理指数による無限根評価で δ 射を構成し、raw 割り算と実完備化の普遍性へ渡す。
原典とは異なる具体的な単項式評価と Witt 座標による証明。

## 規約

源の prism 商の p 正則性や入力のモニック性はこの普遍射には不要。
剰余上の根列の試験 prism 内への一意持上げは引き続き別工程。

## 使われ方

既存の指定 δ 入力射を、基底と実根列のデータから作る。
-/

@[expose] public noncomputable section PowerRootPrismMonicRootUniversal

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
section Evaluation
variable {R : Type u} [CommRing R] (p₀ : ℕ) (hp₀ : 0 < p₀)
variable {B : Type u} [CommRing B] (k : R →+* B)
variable (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p₀ = ρ n)

/-- 概要：無限根評価と通常変数での多項式入力は指定した第零根での通常評価と一致。
方針：環射と多項式評価の可換性を係数公式・第零変数公式で計算する。
規約：入力多項式のモニック性や次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分子の可除性を元の方程式で表す。 -/
theorem powerRootPolynomialEval_baseMap (g : Polynomial R) :
    powerRootPolynomialEval p₀ hp₀ k ρ hρ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap R p₀ hp₀ g) =
      g.eval₂ k (ρ 0) := by
  unfold _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, powerRootPolynomialEval_variable]
  have hc : (powerRootPolynomialEval p₀ hp₀ k ρ hρ).comp
      (algebraMap R (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R p₀ hp₀)) = k := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p₀ hp₀ k ρ hρ
  rw [hc]

end Evaluation

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


/-- 概要：基底 δ 射と互換な rank 1 根列から実完備化への一意な射を作る。
方針：無限根評価 δ 射に raw 実完備化の普遍性を適用し、一意性を係数・根上で確認する。
規約：根列は試験 prism の台環内に与え、剰余からの持上げは仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の指定入力 δ 射を具体的データで置き換える。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hδρ : ∀ n, Q.deltaStructure.delta (ρ n) = 0)
    (hroot : Q.generator ∣ f.eval₂ k (ρ 0)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let g := powerRootPolynomialEval p hp k ρ hρ
  have hg : (E).IsDeltaHom Q.deltaStructure g :=
    powerRootPolynomialEval_isDeltaHom p hW.p_mul_injective W.deltaStructure
      Q.deltaStructure k hk ρ hρ hδρ
  have hdg : g dP = Q.generator := (powerRootPolynomialEval_coeff p hp k ρ hρ W.generator).trans hd
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact Q.generator_regular
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    change g dP ∣ g (powerRootMonicPDInput p f)
    rw [hdg]
    unfold powerRootMonicPDInput
    exact (powerRootPolynomialEval_baseMap p hp k ρ hρ f).symm ▸ hroot
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact Q.complete_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k
    rw [hF.2]
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp k ρ hρ
  · intro n
    exact (RingHom.congr_fun hF.2 (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)).trans
      (powerRootPolynomialEval_variable p hp k ρ hρ n)
  · intro K hK
    apply hu K
    refine ⟨hK.1, ?_⟩
    apply powerRootPolynomial_ringHom_ext p hp
    · have hkg : (K.comp ((uL).comp jL)).comp (algebraMap A P) = k := hK.2.1
      apply RingHom.ext
      intro r
      exact (RingHom.congr_fun hkg r).trans (powerRootPolynomialEval_coeff p hp k ρ hρ r).symm
    · intro n
      exact (hK.2.2 n).trans (powerRootPolynomialEval_variable p hp k ρ hρ n).symm

/-- 概要：p 正則な試験 prism の互換根列から、実完備化への射が一意に存在する。
方針：導来 p 完備性と p 正則性から p 進分離性を得て、根の δ 条件を自動で供給する。
規約：p 正則性は試験 prism の台環に課し、源の prism 商には課さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実根データによる比較射。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_p_regular_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hpB : Function.Injective (fun x : B => (p : B) * x))
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : Q.generator ∣ f.eval₂ k (ρ 0)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n))) = ρ n := by
  let := Q.isAdicComplete_p_of_regular hpB
  exact existsUnique_powerRootPrismMonicCompletionHom_of_roots W hW f Q k hk hd ρ hρ
    (compatiblePowerRoots_delta_eq_zero p Q.deltaStructure ρ hρ) hroot

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicRootUniversal

/-! ## 有界試験 prism の剰余根データによる実完備化の普遍性

## 概要

有界試験 prism の商に互換根列を指定し、その第零根が元の多項式の根なら、
raw 実完備化から試験 prism へ基底と剰余根を保つ δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope 比較の有界試験環での段階。

## 方針

共通完備商で入力 δ 射を一意に持ち上げ、元の raw 割り算・実完備化の普遍性を適用する。
原典とは異なる Perfection のモノイド同型・有理指数評価・W₂ 切断による経路。

## 規約

試験 prism の有界性と指定生成元の一致を明示する。
源の prism 商の p 正則性・入力のモニック性は、この普遍射には不要。
一般の基底 prism 射と絶対 envelope 全体との同定は別工程。

## 使われ方

試験環内の実根列も指定入力 δ 射も引数に残さず、商内の根データから比較射を作る。
-/

@[expose] public noncomputable section PowerRootPrismMonicBoundedResidueRootUniversal

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


/-- 概要：有界試験 prism の剰余根データを保つ実完備化からの δ 射は一意に存在。
方針：一意な入力 δ 持上げで分子の可除性を得て、raw 実完備化の普遍性を使う。
規約：根列は商内だけに指定する。試験 prism の有界性と生成元の一致は前提に残す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism への絶対入力データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_bounded_residue_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k) (ρ 0) = 0) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let qB := Ideal.Quotient.mk Q.ideal
  obtain ⟨g, hg, hgu⟩ :=
    existsUnique_powerRootPolynomialDeltaHom_of_boundedPrism_residue_roots p hW.p_mul_injective
      W.deltaStructure Q hB k hk ρ hρ
  have hdg : g dP = Q.generator := (RingHom.congr_fun hg.2.1 W.generator).trans hd
  have hinput : g (powerRootMonicPDInput p f) =
      f.eval₂ k (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)) := by
    unfold powerRootMonicPDInput _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hg.2.1]
  have hzero : qB (g (powerRootMonicPDInput p f)) = 0 := by
    calc
      _ = qB (f.eval₂ k (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0))) := congrArg qB hinput
      _ = f.eval₂ (qB.comp k) (qB (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0))) :=
        Polynomial.hom_eval₂ f k qB _
      _ = 0 := by
        rw [show qB (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)) = ρ 0 from hg.2.2 0]
        exact hroot
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact Q.generator_regular
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    rw [hdg]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact Q.complete_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg.1 hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k
    rw [hF.2]
    exact hg.2.1
  · intro n
    exact (congrArg qB (RingHom.congr_fun hF.2 (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n))).trans
      (hg.2.2 n)
  · intro K hK
    let gK := K.comp ((uL).comp jL)
    have hKδ : (E).IsDeltaHom Q.deltaStructure gK :=
      hK.1.comp ((pdCompletionUnit_isDeltaHom DL (jL dP)).comp
        (deltaAdjoinDivisionMap_isDeltaHom E dP a))
    have hgK : gK = g := hgu gK ⟨hKδ, hK.2.1, hK.2.2⟩
    exact hu K ⟨hK.1, hgK⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicBoundedResidueRootUniversal

/-! ## 一般の基底 prism 射を保つ実完備化の普遍性

## 概要

有界試験 prism の剰余根データと任意の基底 prism 射から、元の raw 実完備化への
基底・剰余根を保つ δ 射が一意に存在する。BS 著者版 Remark 7.15（著者版 p.62）の envelope 比較。

## 方針

生成元の像の一意な単元係数から正則性・完備性・可除性を供給し、既存の raw 普遍性を使う。
原典とは異なる有界ねじれ・共通完備商・単元係数による経路。

## 規約

選択生成元の厳密な保存は仮定しない。源の prism 商の p 正則性・モニック性も不要。
源 H 自体の prism 性と原典の完備入力環との接続は別工程。

## 使われ方

prism イデアルを保つ一般の基底射を入力とし、剰余根データによる絶対比較へ進む。
-/

@[expose] public noncomputable section PowerRootPrismMonicBasePrismUniversal

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


/-- 概要：有界試験 prism の剰余根データを保つ実完備化からの δ 射は一意に存在。
方針：一意な入力 δ 持上げで分子の可除性を得て、raw 実完備化の普遍性を使う。
規約：根列は商内だけに指定し、基底射はイデアルを保つ任意の prism 射とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism への絶対入力データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_over_bounded_prism
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k.toRingHom) (ρ 0) = 0) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let qB := Ideal.Quotient.mk Q.ideal
  obtain ⟨g, hg, hgu⟩ :=
    existsUnique_powerRootPolynomialDeltaHom_of_boundedPrism_residue_roots p hW.p_mul_injective
      W.deltaStructure Q hB k.toRingHom k.map_delta ρ hρ
  have hdg : g dP = k.toRingHom W.generator := RingHom.congr_fun hg.2.1 W.generator
  have hinput : g (powerRootMonicPDInput p f) =
      f.eval₂ k.toRingHom (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)) := by
    unfold powerRootMonicPDInput _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hg.2.1]
  have hzero : qB (g (powerRootMonicPDInput p f)) = 0 := by
    calc
      _ = qB (f.eval₂ k.toRingHom (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0))) := congrArg qB hinput
      _ = f.eval₂ (qB.comp k.toRingHom) (qB (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0))) :=
        Polynomial.hom_eval₂ f k.toRingHom qB _
      _ = 0 := by
        rw [show qB (g (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 0)) = ρ 0 from hg.2.2 0]
        exact hroot
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact k.map_generator_mul_injective
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    rw [hdg]
    apply Ideal.mem_span_singleton.mp
    rw [k.span_map_generator]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact k.isModuleComplete_map_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg.1 hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k.toRingHom
    rw [hF.2]
    exact hg.2.1
  · intro n
    exact (congrArg qB (RingHom.congr_fun hF.2 (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n))).trans
      (hg.2.2 n)
  · intro K hK
    let gK := K.comp ((uL).comp jL)
    have hKδ : (E).IsDeltaHom Q.deltaStructure gK :=
      hK.1.comp ((pdCompletionUnit_isDeltaHom DL (jL dP)).comp
        (deltaAdjoinDivisionMap_isDeltaHom E dP a))
    have hgK : gK = g := hgu gK ⟨hKδ, hK.2.1, hK.2.2⟩
    exact hu K ⟨hK.1, hgK⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicBasePrismUniversal

/-! ## 通常の方程式商からの入力射による実完備化の普遍性

## 概要

通常の入力環 (A/d)[Y^(1/p^∞)]/(f) から試験 prism の商への射を与えると、
実完備化から試験 prism への基底と入力根を保つ δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の完備入力環との比較への一段階。

## 方針

入力環の標準根の像から互換根列と方程式を抽出し、一般基底 prism 射の普遍性へ渡す。
原典とは異なる通常の商の明示的な普遍性と根列持上げによる経路。

## 規約

入力環はこの段階では未完備。原典の完備入力環との一致や H の prism 性は主張しない。
モニック性・正次数や源の prism 商の p 正則性を前提としない。

## 使われ方

個々の根列の指定を実際の入力環からの環射に置き換える。
-/

@[expose] public noncomputable section PowerRootPrismMonicEquationInput

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
local notation "S" => PowerRootEquationQuotient p hp fR
local notation "cS" => powerRootEquationQuotientCoeff p hp fR
local notation "rS" => powerRootEquationQuotientRoot p hp fR

/-- 概要：通常の方程式商からの入力射を保つ実完備化の δ 射は一意に存在。
方針：標準根の像が満たす互換性と方程式を一般基底射の普遍性に渡す。
規約：通常の商 S と有界試験 prism を使い、原典の完備 S との同定は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力環からの試験データ。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_equation_input
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : S →+* B ⧸ Q.ideal)
    (hη : η.comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) = η (rS n) := by
  have hρ : ∀ n, η (rS (n + 1)) ^ p = η (rS n) := by
    intro n
    exact (map_pow η _ _).symm.trans
      (congrArg η (powerRootEquationQuotientRoot_pow p hp fR n))
  have heq := congrArg η (powerRootEquationQuotientRoot_equation p hp fR)
  rw [Polynomial.hom_eval₂, map_zero, hη, Polynomial.eval₂_map] at heq
  exact existsUnique_powerRootPrismMonicCompletionHom_over_bounded_prism W hW f Q hB k
    (fun n => η (rS n)) hρ heq

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicEquationInput

/-! ## André 方程式商の p 完備化からの入力射

## 概要

通常の方程式商の p 完備化から有界試験 prism の商への射を与えると、
実完備化 H から試験 prism への基底と入力根を保つ δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の完備入力の試験射への接続。

## 方針

完備入力射を通常の商へ制限し、構成済みの一意な δ 射を使う。
原典とは異なる通常の商・完備化の普遍性と根列持上げによる経路。

## 規約

入力は通常の商を先に p 完備化した環。原典の完備多項式環を割る順序との交換は別工程。
源 H 自体の prism 性や絶対 envelope 全体の同定はまだ主張しない。

## 使われ方

p 完備な試験環への入力射を H の普遍性に渡す。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletedEquationInput

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
local notation "S" => PowerRootEquationQuotient p hp fR
local notation "cS" => powerRootEquationQuotientCoeff p hp fR
local notation "rS" => powerRootEquationQuotientRoot p hp fR

local notation "C" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "jS" => algebraMap S C

/-- 概要：方程式商の p 完備化からの入力射を保つ H の δ 射は一意に存在。
方針：入力射を通常の商へ制限して一意な実完備化の射を作る。
規約：入力の完備化を明示し、H 自体の prism 性は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力環の試験射。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_completed_equation_input
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : C →+* B ⧸ Q.ideal)
    (hη : (η.comp jS).comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) = η (jS (rS n)) := by
  exact existsUnique_powerRootPrismMonicCompletionHom_of_equation_input W hW f Q hB k
    (η.comp jS) hη

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletedEquationInput

/-! ## André 原典の順序の完備入力環からの試験射

## 概要

S=(A/d)⟨Y^(1/p^∞)⟩/(f) から有界試験 prism の商への入力射に対し、
元の H から試験 prism への基底と全入力根を保つ δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の完備入力環との接続。

## 方針

モニック商と p 完備化の交換同型で入力射を移し、既存の実完備化の普遍性を適用する。
原典とは異なる全冪商の正則性・通常の完備化と商の普遍性による経路。

## 規約

入力を完備化してからモニック関係で割る。係数環の p 正則性は要求しない。
H 自体の prism 性と絶対 envelope 全体の同定は別工程。

## 使われ方

原典の順序の完備入力射を絶対 envelope の比較に渡す。
-/

@[expose] public noncomputable section PowerRootPrismMonicOriginalCompletedInput

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

/-- 概要：原典の順序の完備入力環からの射を保つ H の δ 射は一意に存在。
方針：全入力元を保つ商と完備化の交換同型で既存の普遍性に帰着する。
規約：モニック性を使い、追加の p 正則性・正次数は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の S からの試験データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_original_completed_input
    (hf : f.Monic)
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) =
              η (lS (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable R p hp n)) := by
  let := pdCompletionCommRing L p (jL dP)
  let e := powerRootMonicCompletedInputEquiv p hp fR (hf.map (Ideal.Quotient.mk W.ideal))
  have he (x : PR) : e.symm (jS (qR x)) = lS x := by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (powerRootMonicCompletedInputEquiv_coeff p hp fR
        (hf.map (Ideal.Quotient.mk W.ideal)) x).symm
  let ηC := η.comp e.symm.toRingHom
  have hc : (ηC.comp jS).comp (powerRootEquationQuotientCoeff p hp fR) =
      k.quotientMap := by
    apply RingHom.ext
    intro x
    change η (e.symm (jS (qR (algebraMap R PR x)))) = k.quotientMap x
    rw [he]
    exact RingHom.congr_fun hη x
  obtain ⟨F, hF, hu⟩ :=
    existsUnique_powerRootPrismMonicCompletionHom_of_completed_equation_input
      W hW f Q hB k ηC hc
  refine ⟨F, ⟨hF.1, hF.2.1, ?_⟩, ?_⟩
  · intro n
    exact (hF.2.2 n).trans (congrArg η (he (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable R p hp n)))
  · intro K hK
    apply hu K
    refine ⟨hK.1, hK.2.1, ?_⟩
    intro n
    change Ideal.Quotient.mk Q.ideal
      (K (uL (jL (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)))) =
        η (e.symm (jS (qR (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable R p hp n))))
    rw [he]
    exact hK.2.2 n

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicOriginalCompletedInput

/-! ## 自然な Hodge–Tate 候補の ϖ 剰余の忠実平坦性

## 概要

無限根モニック実完備化の分母商を T とすると、自然な T/ϖ は R/ϖ 上自由で、正次数なら忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の具体的 pd 剰余からの移送。

## 方針

自然な像イデアル商を既存の二元商へ移し、係数上の可換性を A の代表元で確認する。

## 規約

元の実完備化・基底射を保持し、prism 商の p 正則性はこの剰余平坦性に要求しない。

## 使われ方

分母商の p 正則性と合わせて完全忠実平坦性へ進む。
-/

@[expose] public noncomputable section PowerRootPrismMonicHodgeTateVarpiFlat

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Iv" => Ideal.span {v}
local notation "Rv" => R ⧸ Iv
local notation "S" => H ⧸ Ideal.span {dH, xH}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

/-- 概要：自然な基底射による Hodge–Tate 候補の R 代数構造。
方針：検証済みの基底環射から代数構造を得る。
規約：係数作用を移送で選び直さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常剰余テンソル。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTateAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra R T := by
  let := pdCompletionCommRing L p (jL dP)
  exact (φ).toAlgebra

/-- 概要：自然な像イデアルによる ϖ 商は実完備化の指定二元商と環同型。
方針：像主イデアルを生成元の像で表示し、既存の二重商比較へ移す。
規約：自然な基底射の像イデアルを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な剰余係数作用。 -/
def powerRootPrismMonicHodgeTateVarpiMapQuotEquiv :
    let := pdCompletionCommRing L p (jL dP)
    (T ⧸ Ideal.map φ Iv) ≃+* S := by
  let := pdCompletionCommRing L p (jL dP)
  exact (Ideal.quotEquivOfEq (show Ideal.map φ Iv = Ideal.span {φ v} by
    rw [Ideal.map_span, Set.image_singleton])).trans
      (powerRootPrismMonicHodgeTateVarpiEquiv W hW f)

/-- 概要：像イデアル商の比較は実完備化の代表元を保持する。
方針：像主イデアルの書換えと二重商の代表元公式を使う。
規約：全ての実 H⁰ 元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数線形性。 -/
theorem powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk (t : H) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) = Ideal.Quotient.mk _ t := by
  let := pdCompletionCommRing L p (jL dP)
  have h := principalDoubleQuotEquiv_mk dH xH t
  unfold powerRootPrismMonicHodgeTateVarpiMapQuotEquiv
  change principalDoubleQuotEquiv dH xH
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) = _
  exact h

/-- 概要：自然な像イデアル商の R/ϖ 代数構造を固定する。
方針：標準商代数構造を元の基底射へ適用する。
規約：同じ像イデアルを型に明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常剰余の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTateVarpiAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  exact adicQuotientAlgebra Iv T

/-- 概要：比較先の二元商の標準係数作用を同じ環型で固定する。
方針：既存 pd 剰余の係数作用をそのまま用いる。
規約：係数像の公式は既存のものと同一。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商比較の型検査。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTatePDResidueAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    Algebra Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  with_reducible exact powerRootPrismMonicVarpiResidueAlgebra W hW f hf

set_option maxHeartbeats 2000000 in
-- 二重商と二元商の巨大な実完備化型について、二つの係数構造の照合に必要。
/-- 概要：自然な ϖ 商と既存 pd 剰余の同型は R/ϖ 線形。
方針：R/ϖ の元を A の代表元へ戻し、両側の自然係数像を照合する。
規約：終域の係数作用は既存の標準係数像と一致する作用を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由性と忠実平坦性の移送。 -/
def powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    @AlgEquiv Rv (T ⧸ Ideal.map φ Iv) S
      (inferInstance : CommSemiring Rv)
      (inferInstance : Semiring (T ⧸ Ideal.map φ Iv)) (inferInstance : Semiring S)
      (powerRootPrismMonicHodgeTateVarpiAlgebra W hW f)
      (powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  refine { powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f with commutes' := ?_ }
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
    (Ideal.Quotient.mk _ (φ (Ideal.Quotient.mk W.ideal r))) = _
  rw [powerRootPrismMonicHodgeTateBaseMap_mk,
    powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk]
  exact (powerRootPrismMonicVarpiResidueAlgebra_base_coeff W hW f hf r).symm

/-- 概要：自然な Hodge–Tate 候補の ϖ 商は R/ϖ 上自由。
方針：係数を保つ代数同型で既存 pd 剰余の自由性を戻す。
規約：正次数と prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常剰余平坦性。 -/
theorem powerRootPrismMonicHodgeTateVarpi_free (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Module.Free Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let := powerRootPrismMonicVarpiResidue_free W hW f hf
  exact Module.Free.of_equiv
    (powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf).symm.toLinearEquiv

/-- 概要：正次数モニック入力の自然な Hodge–Tate 候補の ϖ 商は R/ϖ 上忠実平坦。
方針：係数を保つ代数同型で既存 pd 剰余の忠実平坦性を戻す。
規約：prism 商の p 正則性は不要で、正次数を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全忠実平坦性の剰余条件。 -/
theorem powerRootPrismMonicHodgeTateVarpi_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Module.FaithfullyFlat Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let := powerRootPrismMonicVarpiResidue_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Rv S
    (powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicHodgeTateVarpiFlat

/-! ## André Hodge–Tate 商の条件付き ϖ 正則性

## 概要

prism 商が p 正則なら、元のモニック Hodge–Tate 商でも ϖ が正則。
BS 著者版 Remark 7.15（著者版 p.62）の条件付きの中間計算。

## 方針

(ϖ^p)=(p) と条件付きの商の p 正則性から ϖ 正則性を得る。

## 規約

この正則性は一般には無条件化できない。旧完全平坦性の2定理は不要となったので削除し、
完全忠実平坦性の呼出しは 分冪包 の実源の純性による無条件版へ移した。

## 使われ方

A1-c2 の既存の条件付き係数比較が使う正則性を、最終比較が届くまで保持する。
-/

@[expose] public noncomputable section PowerRootPrismMonicHodgeTateCompletelyFlat

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion

/-- 概要：正則元と同じ主イデアルを生成する正冪の底も正則。
方針：主イデアル所属による可除性と積・正冪の正則性を使う。
規約：零環も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の (ϖ^p)=(p) からの正則性。 -/
theorem regular_of_span_power_eq {B : Type u} [CommRing B] (b c : B) (n : ℕ)
    (hn : 0 < n) (he : Ideal.span {b ^ n} = Ideal.span {c}) (hc : IsSMulRegular B c) :
    IsSMulRegular B b := by
  have hm : c ∈ Ideal.span {b ^ n} := by rw [he]; exact Ideal.mem_span_singleton_self c
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hm
  rw [hz, mul_comm] at hc
  exact (IsSMulRegular.pow_iff hn).mp hc.of_mul

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
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

include hpR hf in
/-- 概要：自然な Hodge–Tate 候補で基底の ϖ は正則に作用する。
方針：基底の主イデアル等式を自然な基底射で移し、候補の p 正則性を使う。
規約：正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全平坦性の正則性条件。 -/
theorem powerRootPrismMonicHodgeTate_varpi_regular :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsSMulRegular T v := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  have he : Ideal.span {(φ v) ^ p} = Ideal.span {(p : T)} := by
    simpa only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast] using
      congrArg (Ideal.map φ) (perfectPrismVarpi_span_pow W hW)
  have h := regular_of_span_power_eq (φ v) (p : T) p hp he
    (powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular W hW hpR f hf)
  exact h

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicHodgeTateCompletelyFlat
