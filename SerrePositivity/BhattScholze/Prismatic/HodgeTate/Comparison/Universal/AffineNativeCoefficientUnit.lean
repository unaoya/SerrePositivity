module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverTotalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CanonicalCompletedNaturality
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows

/-!
# 元の完備Tot係数比較と元の導来単位

## 概要
元の半自由完備行の比較を、元の導来単位上で標準増大へ戻す。

## 方針
同じ行射を増大と元の係数射へ分解し、元の標準完備比較の単位の式を使う。

## 規約
元の余単体的比較も元の係数射も置き換えない。

## 使われ方
HT04.R2の指定終域同型と通常係数表示との照合。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal HTComparisonResolution
open HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 元の導来単位に沿った同じ完備Tot係数比較の値。 -/
theorem affineNativeCoefficient_unit
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (r : ℕ) {s : ℕ} (x : Fin s → A) :
    let X := coefficientSingleRows (affineBaseModules P hP r)
    let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
    let C := finiteCompletionFunctor (fun j => f.toRingHom (x j))
    let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
    (finiteDerivedCompletionUnit (fun j => f.toRingHom (x j))).app
      ((complexDerivedExtension f.toRingHom).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ≫
      cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x X 0
        (affineBaseSingleRows_lowerBound P hP r) ≫
      DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x)) =
    (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫
      DerivedCategory.Q.map (baseChangeModelToCompletedRows f.toRingHom x
        ((alternatingCofaceMapComplex (Complex A)).obj X) (𝟙 _)) ≫
      DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
        ((alternatingCofaceFunctorIso (E ⋙ C)).app X).hom) ≫
      DerivedCategory.Q.map (T.map (Functor.whiskerRight
        (affineAnyExtendedSingleRowsMap f hP hQ r) C)) := by
  let X := coefficientSingleRows (affineBaseModules P hP r)
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let C := finiteCompletionFunctor (fun j => f.toRingHom (x j))
  let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
  have ha := cosimplicialNativeComparison_comp_augmentation f.toRingHom x X 0
    (affineBaseSingleRows_lowerBound P hP r)
  simp only [affineResolvedCompletedRowsMap, Functor.map_comp]
  simp only [crystallineResolvedCompletedAugmentation]
  rw [← Category.assoc (cosimplicialNativeCompletedBaseChangeComparison _ _ _ _ _), ha]
  simp only [Category.assoc]
  rw [unit_comp_canonicalCompletedBaseChangeComparison_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
