module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedCompletedSource
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardCompletedModelComparison

/-!
# 元の S 完備比較の完備化前の四角形

## 概要
指定した分解の射と元の S 行単位を含め、固定 R 模型の比較と一致させる。

## 方針
係数増大の自然性・通常の Tot 比較の四角形・係数制限の Tot 自然性を合成する。

## 規約
この四角形には入力や Tot の K-flat 性を要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の単位による標準比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (L : ScalarResolution f)

/-- 元の標準射は、制限後に実際の同じ水平射の Tot となる。 -/
theorem rawCompletedComparison_compatibility {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K) :
    L.comparison P ≫ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (baseChangeModelToCompletedRows f x K q) ≫
      (restrictionTotalIso f (standardCompletedBaseChangeRows f x K)).hom =
    L.tensorFunctor.map q ≫ tensorTotalComparison L.complex K ≫
      (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (L.toRestrictedCompletedRows x K) := by
  have hρ := restrictionTotalComparison_naturality f
    (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))
  change ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))) ≫
      (restrictionTotalIso f (standardCompletedBaseChangeRows f x K)).hom =
    (restrictionTotalIso f ((baseChangeRowsFunctor f).obj K)).hom ≫
      (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)).map
          (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))) at hρ
  dsimp only [baseChangeModelToCompletedRows]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hρ]
  rw [← Category.assoc, ← L.comparison_naturality]
  have ht := congrArg (fun h => L.tensorFunctor.map q ≫ h ≫
    (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)).map
        (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))))
    (L.totalComparison_compatibility K)
  simpa only [toRestrictedCompletedRows, Functor.map_comp, Category.assoc] using ht

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
