module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
public import SerrePositivity.HomologicalAlgebra.ScalarConeModuleQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology

/-!
# 正則加群の各項完備化

## 概要
指定スカラーが正則な加群の主導来完備化は零次数に集中し、その H⁰ でも正則。

## 方針
通常商で計算するスカラー錐と、完備化単位の Koszul 簡約の同型を使う。

## 規約
基底環上の正則性・平坦性・有限性は仮定しない。正則性はもとの加群上で明記する。

## 使われ方
BS 著者版 Theorem 6.4 の各項の完備化と古典的な複体の比較。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)

/-- 正則加群の主導来完備化は零次数のみに集中し、その H⁰ でもスカラーは正則。 -/
theorem moduleCompletionH0_regular_pure (hM : IsSMulRegular M a) :
    let Y := (derivedComplexCompletionFunctor R a).obj ((moduleObjectFunctor R).obj M)
    Y.IsGE 0 ∧ Y.IsLE 0 ∧ IsSMulRegular ((moduleCompletionH0Functor R a).obj M) a := by
  let X := (moduleObjectFunctor R).obj M
  let Y := (derivedComplexCompletionFunctor R a).obj X
  have e : (derivedScalarConeFunctor R a).obj Y ≅
      (moduleObjectFunctor R).obj (modulePowerReduction a M 1) := by
    have ec := derivedComplexCompletionReductionIso R a 1 X
    have eq := derivedScalarConeModuleQuotientIso a M hM 1
    simpa only [pow_one] using ec.symm ≪≫ eq
  apply derived_pure_of_complete_scalarCone_pure a Y
    (derivedComplexCompletionFunctor_isComplete R a X)
  intro i hi
  exact (derivedSingleHomology_isZero (modulePowerReduction a M 1) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e)

/-- 正則加群の主導来完備化を、実際の H⁰ 完備化加群の single 対象で計算する。 -/
def moduleCompletionH0RegularIso (hM : IsSMulRegular M a) :
    (derivedComplexCompletionFunctor R a).obj ((moduleObjectFunctor R).obj M) ≅
      (moduleObjectFunctor R).obj ((moduleCompletionH0Functor R a).obj M) := by
  have h := moduleCompletionH0_regular_pure a M hM
  let := h.1
  let := h.2.1
  exact normalizedPureHomologyIso _ 0

end SerrePositivity.DerivedCompletion
