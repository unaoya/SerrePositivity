module

public import SerrePositivity.BhattScholze.Andre.PrincipalCompletionResidue

/-!
# André E1・E2：実二座標完備化と第二元商での第一元正則性

## 概要

正則対 b,c に対し、実二座標完備化 H⁰ およびその c 商で b は正則。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の完備化計算。

## 方針

第一主完備化の mod b 比較で正則対を保ち、順序交換してから第二主完備化を行う。
第二主完備化の主剰余比較も使い、元の実二座標 H⁰ へ反復比較で戻す。

## 規約

元の Koszul 完備化と標準射を保持する。Noether 性は要求しない。

## 使われ方

無限根モニック raw 包の実完備化と Hodge–Tate 商の p 正則性。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
variable (hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
include hb hc

/-- 概要：第一主完備化でも元の正則対は正則対。
方針：第一元の正則性を古典的比較で、第二元の mod 第一元正則性を剰余比較で移す。
規約：主完備化の元の標準射を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の反復完備化前の順序交換。 -/
theorem principalPair_principalCompletion_pair_regular :
    let := principalCompletionCommRing R b
    let j := principalCompletionUnitRingHom R b
    IsSMulRegular (PrincipalCompletionH0 R b) (j b) ∧
      IsSMulRegular (PrincipalCompletionH0 R b ⧸ Ideal.span {j b})
        (Ideal.Quotient.mk (Ideal.span {j b}) (j c)) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  constructor
  · let e := principalCompletionAdicAlgEquiv R b hb
    apply (ringEquiv_isSMulRegular e.toRingEquiv _).mpr
    change IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
      (e (principalCompletionUnitRingHom R b b))
    rw [principalCompletionAdicAlgEquiv_unit]
    exact isSMulRegular_adicCompletion_span_singleton R b hb
  · apply (ringEquiv_isSMulRegular (principalCompletionResidueEquiv b) _).mpr
    rw [principalCompletionResidueEquiv_unit]
    exact hc

/-- 概要：第一元は実二座標完備化 H⁰ で正則。
方針：第一主完備化で正則対を交換し、第二主完備化での第二元正則性を使う。
規約：元の二座標 H⁰ と標準射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の p 正則性。 -/
theorem principalPair_pairCompletion_first_regular :
    let := pairCompletionCommRing R b c
    IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c b) := by
  let := principalCompletionCommRing R b
  let B := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  have hB := principalPair_principalCompletion_pair_regular b c hb hc
  have hcB := principalPair_principalCompletion_second_regular b c hb hc
  have hbBc := principal_regular_swap (j b) (j c) hB.1 hB.2
  have hi := principalPair_principalCompletion_second_regular (j c) (j b) hcB hbBc
  let := iteratedCompletionCommRing R b c
  let := pairCompletionCommRing R b c
  apply (ringEquiv_isSMulRegular (pairCompletionIteratedEquiv R b c) _).mpr
  rw [pairCompletionIteratedEquiv_unit]
  exact hi

/-- 概要：第二元で割った実二座標完備化でも第一元は正則。
方針：第一主完備化で正則対を交換し、第二主完備化の主剰余比較で戻す。
規約：両方の元は元の環の標準完備化像。
使われ方：BS Rem 7.15（著者版 p.62）の Hodge–Tate 商の p 正則性。 -/
theorem principalPair_pairCompletion_mod_second_first_regular :
    let := pairCompletionCommRing R b c
    let j := pairCompletionUnitRingHom R b c
    IsSMulRegular (PairCompletionH0 R b c ⧸ Ideal.span {j c})
      (Ideal.Quotient.mk (Ideal.span {j c}) (j b)) := by
  let := principalCompletionCommRing R b
  let B := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  have hB := principalPair_principalCompletion_pair_regular b c hb hc
  have hbBc := principal_regular_swap (j b) (j c) hB.1 hB.2
  let := iteratedCompletionCommRing R b c
  have hi : IsSMulRegular (IteratedCompletionH0 R b c ⧸
      Ideal.span {iteratedCompletionUnitRingHom R b c c})
      (Ideal.Quotient.mk (Ideal.span {iteratedCompletionUnitRingHom R b c c})
        (iteratedCompletionUnitRingHom R b c b)) := by
    apply (ringEquiv_isSMulRegular (principalCompletionResidueEquiv (j c)) _).mpr
    change IsSMulRegular (B ⧸ Ideal.span {j c})
      (principalCompletionResidueEquiv (j c)
        (Ideal.Quotient.mk _ (principalCompletionUnitRingHom B (j c) (j b))))
    rw [principalCompletionResidueEquiv_unit]
    exact hbBc
  let := pairCompletionCommRing R b c
  let e := pairCompletionIteratedEquiv R b c
  let eQ := Ideal.quotientEquiv (Ideal.span {pairCompletionUnitRingHom R b c c})
    (Ideal.span {iteratedCompletionUnitRingHom R b c c}) e (by
      rw [Ideal.map_span, Set.image_singleton]
      simp only [e, RingEquiv.coe_toRingHom,
        pairCompletionIteratedEquiv_unit])
  apply (ringEquiv_isSMulRegular eQ _).mpr
  simpa only [eQ, e, Ideal.quotientEquiv_mk, pairCompletionIteratedEquiv_unit] using hi

end SerrePositivity.BhattScholze.Andre
