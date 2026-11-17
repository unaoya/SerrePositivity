module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCoverTargetUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCoverTargetUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryCofaceCompatibility
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget

/-!
# 元の通常Tot係数射と元のHT全複体の係数同型

## 概要
同じ元の係数射を、元のsingle行と元のHT全複体の二つの表示で照合する。

## 方針
元のsingle行Tot同型の係数変更と自然性を使う。

## 規約
元の通常係数同型も指定Tot同型も再定義しない。

## 使われ方
HT04.R2の指定e_targetを通常係数表示と同定する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の通常Tot係数射は、元のHT全複体の同じ通常係数同型を計算する。 -/
theorem affineOrdinaryTotalCoefficient_compatibility
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    let f := Construction61.crystallineCoverMap P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
    E.map (affineBaseSingleTotalPolynomialIso P hP r).inv ≫
      affineOrdinaryTotalCoefficient P hP r ≫ (affineBaseSingleTotalPolynomialIso Q hQ r).hom =
      (affineAnyOrdinaryTotalIso f hP hQ (Construction61.crystallineCover_generator P) r).hom := by

  have h := affineOrdinaryCofaceCoefficient_compatibility (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P) r
  simpa only [affineOrdinaryTotalCoefficient, affineOrdinaryCofaceCoefficient,
    affineBaseSingleRows] using h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
