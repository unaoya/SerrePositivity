module

public import SerrePositivity.BhattScholze.Andre.PDCompletionKilledCoordinates

/-!
# André E1・E2：実完備化の二元係数剰余と未完備の剰余

## 概要

c が (p,d) に属すれば、実導来 (p,c) 完備化 H⁰ の (p,d) 商は元の環の (p,d) 商と環同型。
BS Rem 7.15（著者版 p.62）の Frobenius 側の完備化剰余へ使う。

## 方針

二元係数イデアルの像を計算し、両完備化座標を殺す一般商比較を適用する。

## 規約

c や d の正則性は不要。実 H⁰ と標準単位を保持する。

## 使われ方

c=φ(d) として、完備化後の (p,d) 商を raw 包の (p,d) 商へ戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] (p : ℕ) (c d : A)
local notation "H" => PDCompletionH0 A p c
local notation "uA" => pdCompletionUnit A p c

/-- 概要：二元イデアル (p,d) の完備化像は同じ二つの標準像で生成される。
方針：span の像と環射の自然数保存性を使う。
規約：右辺の p は実 H⁰ 内の自然数。
使われ方：BS Rem 7.15（著者版 p.62）の二元商の係数像の同定。 -/
theorem pdCompletionPairIdeal_map :
    letI := pdCompletionCommRing A p c
    (Ideal.span {(p : A), d}).map uA = Ideal.span {(p : H), uA d} := by
  let := pdCompletionCommRing A p c
  rw [Ideal.map_span, Set.image_pair, map_natCast]

/-- 概要：c が (p,d) に属せば実完備化の (p,d) 商は元の二元商と環同型。
方針：像イデアルの等式と両座標を殺す商の一般同型を合成する。
規約：正則性・非零性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の完備化剰余を未完備の剰余へ戻す。 -/
def pdCompletionPairResidueEquiv (hc : c ∈ Ideal.span {(p : A), d}) :
    letI := pdCompletionCommRing A p c
    (H ⧸ Ideal.span {(p : H), uA d}) ≃+* (A ⧸ Ideal.span {(p : A), d}) := by
  let := pdCompletionCommRing A p c
  exact (Ideal.quotEquivOfEq (pdCompletionPairIdeal_map p c d).symm).trans
    (pdCompletionQuotientEquivOfKilledCoordinates p c (Ideal.span {(p : A), d})
      (Ideal.subset_span (by simp)) hc)

/-- 概要：二元剰余比較同型は標準完備化像を元の代表元へ送る。
方針：像イデアルの商同型と一般商比較の単位公式を使う。
規約：全ての b:A を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の raw 係数を保つ比較。 -/
theorem pdCompletionPairResidueEquiv_unit
    (hc : c ∈ Ideal.span {(p : A), d}) (b : A) :
    letI := pdCompletionCommRing A p c
    pdCompletionPairResidueEquiv p c d hc (Ideal.Quotient.mk _ (uA b)) =
      Ideal.Quotient.mk _ b := by
  let := pdCompletionCommRing A p c
  simp only [pdCompletionPairResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    pdCompletionQuotientEquivOfKilledCoordinates_unit]

end SerrePositivity.BhattScholze.Andre
