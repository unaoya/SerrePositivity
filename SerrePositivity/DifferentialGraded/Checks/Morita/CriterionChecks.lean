module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionPerfectInverse
public import SerrePositivity.DifferentialGraded.Checks.Morita.U16aChecks
public import SerrePositivity.DifferentialGraded.Checks.Morita.CriterionPerfChecks
public import Mathlib.Data.ZMod.Basic

/-! # U16cの実際の右随伴との統合監査

## 概要
Perf判定・全導来拡張・実際の一般右随伴を同時importし、逆関手とunit/counitを検査する。

## 方針
独立した対象・生成添字宇宙と、標数2でも同じ随伴同値の型を確認する。

## 規約と注意
三条件とcompact生成を入力から消さない。U16d全体の受入は別の記録を要する。

## 使われ方
U16c統合の対象ビルド・全主要宣言の直接公理監査。
-/
@[expose] public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
universe u v w z z'
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
  (hH : CriterionDerivedCompactGeneration A E H)

example : kernelDerivedHom A D E K ≅
    (criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH).inverse :=
  kernelMoritaHomIsoInverse A D E K hK G hG H hH

example : (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
      perfectModuleInclusion A D Set.univ ≅
    perfectModuleInclusion A E Set.univ ⋙ kernelDerivedHom A D E K :=
  kernelMoritaPerfInverseIso A D E K hK G hG H hH

example : (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).inverse =
    kernelDerivedHom A D E K := rfl

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (K : Kernel (ZMod 2) D E) (hK : CriterionPerfConditions (ZMod 2) D E K)
    {I : Type z} [Small.{0} I] (G : I → DerivedModuleCategory (ZMod 2) D)
    (hG : CriterionDerivedCompactGeneration (ZMod 2) D G)
    {J : Type z'} [Small.{0} J] (H : J → DerivedModuleCategory (ZMod 2) E)
    (hH : CriterionDerivedCompactGeneration (ZMod 2) E H) :
    IsIso (kernelDerivedUnit (ZMod 2) D E K) ∧ IsIso (kernelDerivedCounit (ZMod 2) D E K) :=
  ⟨kernelMoritaUnit_isIso (ZMod 2) D E K hK G hG H hH,
    kernelMoritaCounit_isIso (ZMod 2) D E K hK G hG H hH⟩

#print axioms kernelMoritaEquivalence
#print axioms kernelMoritaEquivalence_functor
#print axioms kernelMoritaHomIsoInverse
#print axioms kernelMoritaHomIsoInverse_unit
#print axioms kernelMoritaHomIsoInverse_counit
#print axioms kernelMoritaUnit_isIso
#print axioms kernelMoritaCounit_isIso
#print axioms kernelMoritaAdjunctionEquivalence
#print axioms kernelMoritaAdjunctionEquivalence_functor
#print axioms kernelMoritaAdjunctionEquivalence_inverse
#print axioms kernelMoritaAdjunctionEquivalence_unit
#print axioms kernelMoritaAdjunctionEquivalence_counit
#print axioms kernelMoritaPerfInverseActionIso
#print axioms kernelMoritaPerfInverseIso
#print axioms kernelMoritaPerfInverseIso_counit
