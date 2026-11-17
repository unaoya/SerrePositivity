module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverTargetCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.DerivedHomologyComparisonSquare
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinarySquares
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedFormsBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryBaseHomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget

/-!
# 元の指定e_targetを使う同じηの導来正方形

## 概要
同じ元のηの完備した被覆像を、元の通常係数表示と指定終域同型で結ぶ。

## 方針
元の標準比較の自然性と、元の指定e_targetの一致の式を使う。

## 規約
任意に選んだηの係数変更に関する自然性は仮定しない。

## 使われ方
HT04.R2の零次・一次の指定正方形の共通の射。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 同じ元のηと元の指定e_targetの正方形。 -/
theorem affineCompletedCover_ordinary_square
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1) :
    DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η))) ≫
      (affineOriginalCoverTargetIso P hP 1 hF hR).hom =
    (affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P) ≫
      DerivedCategory.Q.map (((affineOrdinaryCoverFunctor P 1).map η) ≫
        (affineAnyOrdinaryTotalIso (Construction61.crystallineCoverMap P) hP
          (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P) 1).hom) := by
  let τ := DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
    ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))
  let o := affineAnyOrdinaryTotalIso (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P) 1
  have hT := congrArg (fun k => τ ≫ k) (affineOriginalCoverTargetIso_eq_ordinary P hP 1 hF hR)
  have hN := (affineCoverOrdinaryComparison P 1).naturality η
  change τ ≫ (affineCoverOrdinaryComparison P 1).app (affineHTTotalComplex P hP 1) =
    (affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P) ≫
      DerivedCategory.Q.map ((affineOrdinaryCoverFunctor P 1).map η) at hN
  have hN' := congrArg (fun k => k ≫ DerivedCategory.Q.map o.hom) hN
  dsimp only [o] at hN'
  simp only [Category.assoc] at hN'
  have h := hT.trans hN'
  simpa only [τ, Functor.map_comp, Category.assoc] using h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
