module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootHodgeTateReduction
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PrimeReductionPurity

/-!
# André E1・E2：任意のモニック入力の Hodge–Tate 商の完備性

## 概要

元の実完備化 H の標準分母商は、次数零を含む全モニック入力について p 完備。
BS Rem 7.15（著者版 p.62）の prismatic 源の商の完備性を述べる。

## 方針

正次数では同じ商の有界 p ねじれと導来完備性、次数零では同じ H の零環性を使う。
原典の p ねじれなしへの帰着とは異なる純性と有界ねじれによる証明経路。

## 規約

prism 商の p 正則性も入力の正次数も追加せず、元の H と通常商を保持する。

## 使われ方

旧 hpR 付きの完備性公開名を、同じ型から hpR だけを除いて提供する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "dL" => deltaAdjoinDivisionMap E dP a dP
local notation "H" => PDCompletionH0 Raw p dL

include hf in
/-- 概要：無限根モニック実完備化の分母商は通常の意味でも p 完備。
方針：正次数では有界ねじれによる比較、次数零では零環の完備性を使う。
規約：標準分母像による元の通常商を使い、hpR と正次数を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の prismatic 源の完備商。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete :
    let := pdCompletionCommRing Raw p dL
    let T := H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}
    IsAdicComplete (Ideal.span {(p : T)}) T := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p dL
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    infer_instance
  · exact powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete_of_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

end SerrePositivity.BhattScholze.Andre
