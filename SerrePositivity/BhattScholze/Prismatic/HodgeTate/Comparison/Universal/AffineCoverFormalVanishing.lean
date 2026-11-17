module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCompletedCoverModelIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverTargetAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 同じ形式模型の完備被覆像の消滅

## 概要
元の形式模型の完備被覆像は零次・一次以外にホモロジーを持たない。

## 方針
元の標準増大比較と元の模型の自然同型で、通常被覆像の既知の消滅を運ぶ。

## 規約
終域のHT同型も一般の結晶比較も仮定しない。

## 使われ方
HT04.R2の正方形と合わせる、残りの次数の検査。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonResolution HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の指定分解の完備被覆像は零次・一次以外では零。 -/
theorem affineResolvedCoverFormal_homology_isZero
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Construction61.crystallineCoverRing P)) i).obj
        (DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj
          ((complexResolutionFunctor A).obj
            (affineComplexOnBase P 1 (affineLineFormalModel P)))))) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  haveI := affineLineFormalCoverOrdinaryComparison_isIso P hP
  let e := H.mapIso (asIso ((affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app
      ((affineOrdinaryCoverFunctor P 1).obj (affineLineFormalModel P))
  exact (affineLineFormalOrdinary_homology_isZero P (Construction61.crystallineCoverMap P).toRingHom
    i h0 h1).of_iso e

/-- 同じ完備導来関手の形式模型の像も零次・一次以外では零。 -/
theorem affineNativeCoverFormal_homology_isZero
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Construction61.crystallineCoverRing P)) i).obj
        ((finiteDerivedCompletionFunctor (coverImageCoordinates P)).obj
          ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).obj
            (DerivedCategory.Q.obj (affineComplexOnBase P 1 (affineLineFormalModel P)))))) := by
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{u} (Construction61.crystallineCoverRing P)) i
  exact (affineResolvedCoverFormal_homology_isZero P hP i h0 h1).of_iso
    (H.mapIso ((affineNativeCompletedCoverModelIso P).app
      (affineComplexOnBase P 1 (affineLineFormalModel P))))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
