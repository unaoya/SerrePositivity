module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CanonicalCompletedNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows

/-!
# 元の増大から標準完備比較の同型性を戻す

## 概要
元の余単体的分解の比較と完備した増大が同型なら、模型を選ばない元の比較も同型になる。

## 方針
元の比較と増大の合成の式から、交代余面複体の標準関手同型を外す。

## 規約
増大は同じ元の分解の標準増大であり、任意の射を選ばない。

## 使われ方
指定被覆でのTorの検査を、元のHT複体の標準比較に接続する。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open HomologicalAlgebra DifferentialGraded DerivedCompletion HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の増大のTotが擬同型なら、元の分解比較の同型性を元の標準比較へ戻せる。 -/
theorem canonicalCosimplicialComparison_isIso_of_augmentation (f : R →+* S)
    {r : ℕ} (x : Fin r → R) (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → CategoryTheory.Limits.IsZero
      ((X.obj (SimplexCategory.mk n)).homology i))
    (hn : IsIso (cosimplicialNativeCompletedBaseChangeComparison f x X b hX))
    (ha : QuasiIso ((alternatingCofaceMapComplex (Complex S) ⋙
      cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        (crystallineResolvedCompletedAugmentation f x X))) :
    IsIso (canonicalCompletedBaseChangeComparison f x
      ((alternatingCofaceMapComplex (Complex R)).obj X)) := by
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
    finiteCompletionFunctor (fun j => f (x j))
  let T := alternatingCofaceMapComplex (Complex S) ⋙
    cochainProductTotalizationFunctor (ModuleCat.{u} S)
  letI := hn
  have haug : IsIso (DerivedCategory.Q.map (T.map
      (crystallineResolvedCompletedAugmentation f x X))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr ha
  letI := haug
  have he := cosimplicialNativeComparison_comp_augmentation f x X b hX
  have hc : IsIso (canonicalCompletedBaseChangeComparison f x
      ((alternatingCofaceMapComplex (Complex R)).obj X) ≫
      DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        ((alternatingCofaceFunctorIso E).app X).hom)) := by
    rw [← he]
    exact inferInstanceAs (IsIso (cosimplicialNativeCompletedBaseChangeComparison f x X b hX ≫
      DerivedCategory.Q.map (T.map (crystallineResolvedCompletedAugmentation f x X))))
  letI := hc
  exact IsIso.of_isIso_comp_right _
    (DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
      ((alternatingCofaceFunctorIso E).app X).hom))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
