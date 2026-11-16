module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates

/-!
# 元のHT全複体の被覆模型と元の被覆のHT全複体

## 概要
元の半自由分解に完備被覆関手を適用した対象を、被覆上の元のHT全複体へ戻す。

## 方針
標準導来係数拡大の模型同型、元のTot比較、元の厳密な完備行の指定射を順に合成する。

## 規約
同型はConstruction6.1の指定された二つの入力だけを使う。一般結晶の比較を仮定しない。

## 使われ方
元のηの終域を、標準係数射と両立する被覆上の終域へ移す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元のHT全複体の同じ半自由分解の、指定された被覆模型の終域同型。 -/
def affineOriginalCoverTargetIso
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj
      ((complexResolutionFunctor A).obj
        (affineComplexOnBase P r (affineHTTotalComplex P hP r)))) ≅
      DerivedCategory.Q.obj (affineComplexOnBase (Construction61.crystallineCover P) r
        (affineHTTotalComplex (Construction61.crystallineCover P)
          (Construction61.crystallineCover_bounded P) r)) := by
  let K := affineComplexOnBase P r (affineHTTotalComplex P hP r)
  haveI := affineOriginalCoverTotalComparison_isIso P hP r hF hR
  exact (coverImageCompletionNatIso P).symm.app ((complexResolutionFunctor A).obj K) ≪≫
    (nativeCompletedScalarModelIso (Construction61.crystallineCoverMap P).toRingHom
      ![(p : A), P.generator] (complexResolutionAugmentation A |>.app K)
      (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)).symm ≪≫
    asIso (affineOriginalCoverTotalComparison P hP r) ≪≫
    affineCoverResolvedTotalIso P hP r ≪≫
    DerivedCategory.Q.mapIso (affineBaseSingleTotalPolynomialIso (Construction61.crystallineCover P)
      (Construction61.crystallineCover_bounded P) r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
