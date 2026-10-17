module

public import SerrePositivity.BhattScholze.Andre.Unoriented.Initial
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicAbsoluteUniversal

/-!
# 元の André 源の向きなし入力圏での初期性

## 概要
BS Rem 7.15（著者版 p.62）の元の源 H の初期性を固定完全基底上の向きなし入力圏へ移す。

## 方針
向き付き入力圏との証明済みの同値に初期性を沿わせる。

## 規約
元の正次数モニック性だけを引き継ぎ、hpR・正則性・有界性を追加しない。

## 使われ方
向きなしの任意の初期対象と元の H の比較に使う。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "R" => A ⧸ W.ideal

local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)

open CategoryTheory CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

/-- 概要：元の正次数モニック源を向きなし入力対象とする。
方針：既存の源に忘却関手を適用する。
規約：台環・δ 構造・基底・入力作用を保持する。
使われ方：BS Rem 7.15（p.62）の向きなしの標準源。 -/
def powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented :
    BoundedPrismInputUnoriented W cS :=
  (BoundedPrismInputUnoriented.forgetFunctor (W := W) (c := cS) hW).obj
    (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)

/-- 概要：元の正次数モニック源は向きなし入力圏で初期。
方針：圏同値による初期性の保存を使う。
規約：既存の hdeg を保持し、追加条件を置かない。
使われ方：BS Rem 7.15（p.62）の固定基底上の向きなし普遍性。 -/
def powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented :
    IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg) :=
  powerRootPrismMonicSourceInput_initial_unoriented W hW f hf hdeg

/-- 概要：向きなし入力圏の任意の初期対象と元の H は環同型。
方針：初期対象の一意な同型を標準 orientation 関手で実環の同型へ戻す。
規約：比較先にはその初期性だけを要求する。
使われ方：BS Rem 7.15（p.62）の向きなし envelope の一意性。 -/
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
使われ方：BS Rem 7.15（p.62）の入力作用の照合。 -/
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
使われ方：BS Rem 7.15（p.62）の基底射を指定しない入力作用の普遍性。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented
    (Q : BoundedPrismInputUnoriented W cS) (η : SI →+* Q.ring ⧸ Q.ideal) :
    let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
    ∃! G : OrientedPrism.Hom X.prism Q.orient.prism,
      G.quotientMap.comp X.input = (Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η :=
  existsUnique_powerRootPrismMonicPrismHom_of_absolute_input W hW f hf hdeg
    Q.orient.prism Q.orient.bounded ((Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η)

end SerrePositivity.BhattScholze.Andre
