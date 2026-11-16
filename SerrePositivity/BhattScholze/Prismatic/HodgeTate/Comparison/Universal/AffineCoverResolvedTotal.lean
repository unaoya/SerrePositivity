module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverComparison
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元の被覆上の標準完備行比較とTot

## 概要
元の半自由完備行の指定係数射は各項で擬同型であり、同じ指定比較を元の積Totへ移せる。

## 方針
元の行のTor消滅、標準増大、同じ通常係数射の同型性を使い、標準完備化単位で終域を戻す。

## 規約
全て元の厳密な余単体的射を使う。項ごとの任意の同型から図式の比較を仮定しない。

## 使われ方
HT04.R1の被覆上の元の標準比較を、元のHT全複体へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
open HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の被覆に対する、同じ標準の厳密な半自由完備行の射。 -/
abbrev affineCoverResolvedRowsMap :=
  affineResolvedCompletedRowsMap (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) r ![(p : A), P.generator]

/-- 元の被覆への指定行比較は、各行で擬同型となる。 -/
theorem affineCoverResolvedRowsMap_quasiIso (n : SimplexCategory) :
    QuasiIso ((affineCoverResolvedRowsMap P hP r).app n) :=
  affineResolvedCompletedRowsMap_quasiIso (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P)
    r ![(p : A), P.generator] (affineReducedCover_scalarExtensionTorVanishing P hP r) n

/-- 元の被覆上の剰余行は、被覆の像の二座標で完備。 -/
theorem affineCoverRows_complete (n : SimplexCategory) (j : Fin 2) :
    IsModuleComplete (Construction61.crystallineCoverRing P) (coverImageCoordinates P j)
      ((affineBaseModules (Construction61.crystallineCover P)
        (Construction61.crystallineCover_bounded P) r).obj n) := by
  exact (isComplete_associated_iff _ _ (coverImageCoordinates_associated P j) _).mpr
    (affineBaseModules_complete (Construction61.crystallineCover P)
      (Construction61.crystallineCover_bounded P) r n)

/-- 元の被覆上の完備行のTotを、元の被覆上の剰余行のTotへ指定された射で戻す。 -/
def affineCoverResolvedTotalIso :
    DerivedCategory.Q.obj (cosimplicialTotal (resolvedCompletedBaseChange
      (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator]
        (coefficientSingleRows (affineBaseModules P hP r)))) ≅
      DerivedCategory.Q.obj (cosimplicialTotal (coefficientSingleRows
        (affineBaseModules (Construction61.crystallineCover P)
          (Construction61.crystallineCover_bounded P) r))) :=
  affineResolvedCompletedTotalIso (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P)
    r ![(p : A), P.generator] (affineReducedCover_scalarExtensionTorVanishing P hP r)
      (affineCoverRows_complete P r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
