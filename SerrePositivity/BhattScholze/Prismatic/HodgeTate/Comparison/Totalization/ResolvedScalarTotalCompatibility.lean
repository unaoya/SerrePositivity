module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ScalarTotalCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolvedScalarExtension

/-!
# 任意の固定係数分解と元の S 線形標準比較の四角形

## 概要
実際の係数分解の増大に沿って、固定 R 模型の標準比較が元の S 線形標準射に移ることを示す。

## 方針
零次数係数の照合とテンソル比較の係数についての自然性を合成する。

## 規約
係数分解に S 作用を要求せず、入力の K-flat 性もこの四角形には要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の標準射の保存の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (L : ScalarResolution f)

/-- 各行に元の係数分解の増大による比較を施す。 -/
def comparisonRows (K : CochainComplex (Complex R) ℕ) :
    tensorRows L.complex K ⟶ restrictedRows f
      ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)).obj K) where
  f n := L.comparison (K.X n)
  comm' i j _ := (L.comparison_naturality (K.d i j)).symm

/-- 行比較も、同じ係数増大と元の係数制限同型との合成そのものである。 -/
theorem comparisonRows_eq (K : CochainComplex (Complex R) ℕ) :
    L.comparisonRows K = tensorRowsCoefficientMap L.augmentation K ≫ (restrictedBaseChangeRowsIso f K).inv := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

/-- 固定係数分解の標準比較は、元の S 線形比較を係数制限した標準射に移る。 -/
theorem totalComparison_compatibility (K : CochainComplex (Complex R) ℕ) :
    L.comparison (total K) ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map (baseChangeTotalComparison f K) ≫
        (restrictionTotalIso f ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
          (.up ℕ)).obj K)).hom =
      tensorTotalComparison L.complex K ≫
        (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (L.comparisonRows K) := by
  dsimp only [comparison]
  change cochainTensorMap L.augmentation (𝟙 (total K)) ≫
      (restrictedBaseChangeComplexIso f (total K)).inv ≫ _ ≫ _ = _
  rw [scalarSingle_totalComparison_compatibility, ← Category.assoc,
    tensorTotalComparison_coefficient_naturality, Category.assoc, ← Functor.map_comp,
    ← comparisonRows_eq]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
