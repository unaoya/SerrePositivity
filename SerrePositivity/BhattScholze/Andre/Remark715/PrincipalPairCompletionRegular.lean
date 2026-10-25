module

public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalPairPowerRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# André E1・E2：実二座標完備化での第二元の正則性

## 概要

正則対 b,c の第二元は、実二座標導来完備化の H⁰ でも正則。
BS Rem 7.15（著者版 p.62）の分母の新しいねじれの排除。

## 方針

第一主完備化を古典的完備化へ移して c の正則性を示す。
その実 H⁰ を c で再び完備化し、標準写像を保つ反復比較で戻す。

## 規約

実 Koszul 完備化の H⁰ と標準射を使う。第一元の正則性の保存は別の主張。

## 使われ方

無限根モニック raw 包の実完備化の分母正則性。
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

/-- 概要：第二元は第一元の実主完備化 H⁰ で正則。
方針：標準射を保つ古典的完備化比較で主冪商の計算を移す。
規約：元の実 H⁰ を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の反復完備化の入力。 -/
theorem principalPair_principalCompletion_second_regular :
    let := principalCompletionCommRing R b
    IsSMulRegular (PrincipalCompletionH0 R b) (principalCompletionUnitRingHom R b c) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  let e := principalCompletionAdicAlgEquiv R b hb
  apply (ringEquiv_isSMulRegular e.toRingEquiv _).mpr
  change IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
    (e (principalCompletionUnitRingHom R b c))
  rw [principalCompletionAdicAlgEquiv_unit]
  exact principalPair_adicCompletion_second_regular b c hb hc

/-- 概要：第二元は実二座標導来完備化 H⁰ で正則。
方針：第一主完備化での正則性から第二主完備化で消去し、実反復同型で戻す。
規約：標準射の第二元の像を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の分母正則性。 -/
theorem principalPair_pairCompletion_second_regular :
    let := pairCompletionCommRing R b c
    IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c c) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  let B := PrincipalCompletionH0 R b
  let cb := principalCompletionUnitRingHom R b c
  have hcb : IsSMulRegular B cb := principalPair_principalCompletion_second_regular b c hb hc
  let := iteratedCompletionCommRing R b c
  let := principalCompletionAlgebra B cb
  have hi : IsSMulRegular (IteratedCompletionH0 R b c)
      (iteratedCompletionUnitRingHom R b c c) := by
    have hs := principalCompletionH0_smul_injective_of_regular B cb hcb
    intro x y hxy
    apply hs
    change cb • x = cb • y
    change principalCompletionUnitRingHom B cb cb * x =
      principalCompletionUnitRingHom B cb cb * y at hxy
    change (principalCompletionH0_isCompleteModuleReflection B cb).mul
      ((principalCompletionH0_isCompleteModuleReflection B cb).unitRingHom cb) x =
      (principalCompletionH0_isCompleteModuleReflection B cb).mul
        ((principalCompletionH0_isCompleteModuleReflection B cb).unitRingHom cb) y at hxy
    simpa only [IsCompleteModuleReflection.unitRingHom_apply,
      IsCompleteModuleReflection.mul_scalar_unit] using hxy
  let := pairCompletionCommRing R b c
  let e := pairCompletionIteratedEquiv R b c
  apply (ringEquiv_isSMulRegular e _).mpr
  simpa only [e, pairCompletionIteratedEquiv_unit] using hi

end SerrePositivity.BhattScholze.Andre
