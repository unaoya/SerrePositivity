module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCompletedCoverModelIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverZeroSquare
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverOneSquare

/-!
# 元の完備導来関手の型での指定正方形

## 概要
元の指定模型の正方形を、型つき一覧の完備導来関手の射の等式へ戻す。

## 方針
元の同じ指定模型の自然同型で零次・一次の等式を運ぶ。

## 規約
一次の向きの単位の逆も、元の指定終域同型も保持する。

## 使われ方
HT04.R2の型つき一覧の二つの正方形。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の完備導来被覆関手の零次の指定正方形。 -/
theorem affineNativeCover_zero_square
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (hη : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let v := (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose
    letI := Module.compHom (affineForms Q 1 0) (affineBaseToPolynomialMap Q 1)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
    let c := affineNativeCompletedCoverModelIso P
    let K := affineComplexOnBase P 1 (affineLineFormalModel P)
    let L := affineComplexOnBase P 1 (affineHTTotalComplex P hP 1)
    H.map ((finiteDerivedCompletionFunctor (coverImageCoordinates P)).map
      ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).map
        (DerivedCategory.Q.map ((affineRestrictedComplexFunctor P 1).map η)))) ≫
      H.map (c.app L).hom ≫ (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 0).hom =
    H.map (c.app K).hom ≫ (affineOriginalCoverSourceZeroIso P hP).hom ≫ ModuleCat.ofHom (affineBaseHTMap Q hQ 1 0) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 0
  have hn := congrArg H.map (affineNativeCompletedCoverModelIso_naturality P
    ((affineRestrictedComplexFunctor P 1).map η))
  simp only [Functor.map_comp] at hn
  have hp := congrArg (fun q => q ≫
    (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 0).hom) hn
  simp only [Category.assoc] at hp
  have hz := congrArg (fun q =>
    H.map ((affineNativeCompletedCoverModelIso P).hom.app
      (affineComplexOnBase P 1 (affineLineFormalModel P))) ≫ q)
    (affineOriginalCover_zero_square P hP hF hR η hη)
  simpa only [Category.assoc, Iso.app_hom] using hp.trans hz

/-- 元の完備導来被覆関手の一次の指定正方形。 -/
theorem affineNativeCover_one_square
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (hη : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let v := (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose
    letI := Module.compHom (affineForms Q 1 1) (affineBaseToPolynomialMap Q 1)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1
    let c := affineNativeCompletedCoverModelIso P
    let K := affineComplexOnBase P 1 (affineLineFormalModel P)
    let L := affineComplexOnBase P 1 (affineHTTotalComplex P hP 1)
    H.map ((finiteDerivedCompletionFunctor (coverImageCoordinates P)).map
      ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).map
        (DerivedCategory.Q.map ((affineRestrictedComplexFunctor P 1).map η)))) ≫
      H.map (c.app L).hom ≫ (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 1).hom =
    H.map (c.app K).hom ≫ (affineOriginalCoverSourceOneIso P hP).hom ≫ ModuleCat.ofHom
      ((((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :
        affineForms Q 1 1 →ₗ[B] (affineBaseComplex Q hQ 1).homology 1) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 1
  have hn := congrArg H.map (affineNativeCompletedCoverModelIso_naturality P
    ((affineRestrictedComplexFunctor P 1).map η))
  simp only [Functor.map_comp] at hn
  have hp := congrArg (fun q => q ≫
    (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 1).hom) hn
  simp only [Category.assoc] at hp
  have hz := congrArg (fun q =>
    H.map ((affineNativeCompletedCoverModelIso P).hom.app
      (affineComplexOnBase P 1 (affineLineFormalModel P))) ≫ q)
    (affineOriginalCover_one_square P hP hF hR η hη)
  simpa only [Category.assoc, Iso.app_hom] using hp.trans hz

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
